import Katznelson.Counting.RowLattice
import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.RingTheory.Ideal.Quotient.Index

/-!
# Echelon representatives and the paper's support family

The manuscript abbreviates “echelon” to mean a row-reduced echelon matrix of
maximal rank (lines 177--183).  The existing row-space development indexes the
same objects by their rational row spaces; this file restores the manuscript's
echelon representative as an explicit type.  Any identification of the two
indexing systems is kept as a separate bridge rather than being built into a
definition.
-/

namespace Katznelson

open Set
open scoped Classical NumberField nonZeroDivisors

section

variable {K : Type*} [Field K] [NumberField K]

/- The paper's “echelon” matrices: reduced row echelon and full row rank. -/
def EchelonMatrix (K : Type*) [Field K] (l m : ℕ) :=
  {D : M l m K // D.IsReducedRowEchelon ∧ D.rank = l}

/- The rational row space represented by an echelon matrix. -/
noncomputable def echelonRowSpace {l m : ℕ} (D : EchelonMatrix K l m) :
    Grassmannian K m l :=
  ⟨Submodule.span K (Set.range D.1.row), by
    rw [← Matrix.rank_eq_finrank_span_row]
    exact D.2.2⟩

theorem echelon_rows_linearIndependent {l m : ℕ}
    (D : EchelonMatrix K l m) :
    LinearIndependent K D.1.row := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  rw [Set.finrank, ← Matrix.rank_eq_finrank_span_row, D.2.2]
  simp

theorem exists_echelon_leadingEntry {l m : ℕ}
    (D : EchelonMatrix K l m) (i : Fin l) :
    ∃ c : Fin m, D.1.IsLeadingEntry i c := by
  apply Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp
  exact (echelon_rows_linearIndependent D).ne_zero i

/- A chosen leading column for every row.  The choice is only used to state
   structural consequences of the manuscript's reduced-echelon hypothesis;
   no representative-existence statement is hidden here. -/
noncomputable def echelonLeadingColumn {l m : ℕ}
    (D : EchelonMatrix K l m) : Fin l → Fin m := fun i =>
  (exists_echelon_leadingEntry D i).choose

theorem echelonLeadingColumn_isLeadingEntry {l m : ℕ}
    (D : EchelonMatrix K l m) (i : Fin l) :
    D.1.IsLeadingEntry i (echelonLeadingColumn D i) :=
  (exists_echelon_leadingEntry D i).choose_spec

theorem echelonLeadingColumn_strictMono {l m : ℕ}
    (D : EchelonMatrix K l m) {i i' : Fin l} (hii' : i < i') :
    echelonLeadingColumn D i < echelonLeadingColumn D i' := by
  apply lt_of_not_ge
  intro hnot
  have hle : echelonLeadingColumn D i' ≤ echelonLeadingColumn D i :=
    hnot
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hzero : D.1 i' (echelonLeadingColumn D i') = 0 :=
      D.2.1.isRowEchelon hii' (fun j hj =>
        (echelonLeadingColumn_isLeadingEntry D i).1 j
          (hj.trans hlt))
    exact (echelonLeadingColumn_isLeadingEntry D i').2 hzero
  · have hzero := D.2.1.eq_zero hii'
      (echelonLeadingColumn_isLeadingEntry D i')
    rw [heq] at hzero
    rw [D.2.1.eq_one (echelonLeadingColumn_isLeadingEntry D i)] at hzero
    exact one_ne_zero hzero

theorem rowSpace_nonzero_has_echelon_pivot_leadingEntry
    {l m : ℕ} (D : EchelonMatrix K l m) {x : Fin m → K}
    (hx : x ∈ Submodule.span K (Set.range D.1.row)) (hx0 : x ≠ 0) :
    ∃ i : Fin l,
      (∀ j < echelonLeadingColumn D i, x j = 0) ∧
        x (echelonLeadingColumn D i) ≠ 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
  have hc0 : c ≠ 0 := by
    intro hc'
    apply hx0
    exact hc.symm.trans (by simp [hc'])
  obtain ⟨i₀, hi₀, hmin⟩ :=
    wellFounded_lt.has_min {i : Fin l | c i ≠ 0} (Function.ne_iff.mp hc0)
  have hxeq (j : Fin m) :
      x j = ∑ i : Fin l, c i * (D.1 : M l m K) i j := by
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply]
      using (congrFun hc j).symm
  have hterm_zero (i : Fin l) (j : Fin m)
      (hj : j < echelonLeadingColumn D i₀) :
      c i * (D.1 : M l m K) i j = 0 := by
    by_cases hci : c i = 0
    · simp [hci]
    · have hnotlt : ¬ i < i₀ := fun hlt => (hmin i hci) hlt
      have hle : i₀ ≤ i := le_of_not_gt hnotlt
      by_cases hie : i₀ = i
      · subst i
        rw [(echelonLeadingColumn_isLeadingEntry D i₀).1 j hj]
        simp
      · have hil : i₀ < i := lt_of_le_of_ne hle hie
        have hpil := echelonLeadingColumn_strictMono D hil
        rw [(echelonLeadingColumn_isLeadingEntry D i).1 j
          (hj.trans hpil)]
        simp
  refine ⟨i₀, ?_, ?_⟩
  · intro j hj
    rw [hxeq]
    exact Finset.sum_eq_zero (fun i hi => hterm_zero i j hj)
  · rw [hxeq, Finset.sum_eq_single i₀]
    · simpa [D.2.1.eq_one (echelonLeadingColumn_isLeadingEntry D i₀)]
        using hi₀
    · intro i hi hne
      by_cases hci : c i = 0
      · simp [hci]
      · have hnotlt : ¬ i < i₀ := fun hlt => (hmin i hci) hlt
        have hle : i₀ ≤ i := le_of_not_gt hnotlt
        have hil : i₀ < i := lt_of_le_of_ne hle (Ne.symm hne)
        have hpil := echelonLeadingColumn_strictMono D hil
        rw [(echelonLeadingColumn_isLeadingEntry D i).1 _ hpil]
        simp
    · simp

theorem echelonLeadingColumn_range_eq_of_rowSpace_eq
    {l m : ℕ} {D E : EchelonMatrix K l m}
    (hDE : echelonRowSpace D = echelonRowSpace E) :
    Set.range (echelonLeadingColumn D) = Set.range (echelonLeadingColumn E) := by
  apply Set.Subset.antisymm
  · rintro p ⟨i, rfl⟩
    have hspan : Submodule.span K (Set.range D.1.row) =
        Submodule.span K (Set.range E.1.row) := congrArg Subtype.val hDE
    have hxi : D.1.row i ∈ Submodule.span K (Set.range E.1.row) := by
      have hxi' : D.1.row i ∈ Submodule.span K (Set.range D.1.row) :=
        Submodule.subset_span ⟨i, rfl⟩
      rw [hspan] at hxi'
      exact hxi'
    have hxi0 : D.1.row i ≠ 0 :=
      (echelonLeadingColumn_isLeadingEntry D i).row_ne_zero
    obtain ⟨j, hjzero, hjnezero⟩ :=
      rowSpace_nonzero_has_echelon_pivot_leadingEntry E hxi hxi0
    have hpi : D.1.IsLeadingEntry i (echelonLeadingColumn D i) :=
      echelonLeadingColumn_isLeadingEntry D i
    have hpj : echelonLeadingColumn E j = echelonLeadingColumn D i := by
      apply le_antisymm
      · apply le_of_not_gt
        intro hlt
        exact hpi.2 (hjzero _ hlt)
      · apply le_of_not_gt
        intro hlt
        exact hjnezero (hpi.1 _ hlt)
    exact ⟨j, hpj⟩
  · rintro p ⟨i, rfl⟩
    have hspan : Submodule.span K (Set.range E.1.row) =
        Submodule.span K (Set.range D.1.row) := congrArg Subtype.val hDE.symm
    have hxi : E.1.row i ∈ Submodule.span K (Set.range D.1.row) := by
      have hxi' : E.1.row i ∈ Submodule.span K (Set.range E.1.row) :=
        Submodule.subset_span ⟨i, rfl⟩
      rw [hspan] at hxi'
      exact hxi'
    have hxi0 : E.1.row i ≠ 0 :=
      (echelonLeadingColumn_isLeadingEntry E i).row_ne_zero
    obtain ⟨j, hjzero, hjnezero⟩ :=
      rowSpace_nonzero_has_echelon_pivot_leadingEntry D hxi hxi0
    have hpi : E.1.IsLeadingEntry i (echelonLeadingColumn E i) :=
      echelonLeadingColumn_isLeadingEntry E i
    have hpj : echelonLeadingColumn D j = echelonLeadingColumn E i := by
      apply le_antisymm
      · apply le_of_not_gt
        intro hlt
        exact hpi.2 (hjzero _ hlt)
      · apply le_of_not_gt
        intro hlt
        exact hjnezero (hpi.1 _ hlt)
    exact ⟨j, hpj⟩

theorem echelonLeadingColumn_eq_of_rowSpace_eq
    {l m : ℕ} {D E : EchelonMatrix K l m}
    (hDE : echelonRowSpace D = echelonRowSpace E) :
    echelonLeadingColumn D = echelonLeadingColumn E := by
  let pD : Fin l ↪o Fin m :=
    OrderEmbedding.ofStrictMono (echelonLeadingColumn D)
      (fun _ _ h => echelonLeadingColumn_strictMono D h)
  let pE : Fin l ↪o Fin m :=
    OrderEmbedding.ofStrictMono (echelonLeadingColumn E)
      (fun _ _ h => echelonLeadingColumn_strictMono E h)
  have hpD : (pD : Fin l → Fin m) = echelonLeadingColumn D := by
    dsimp [pD]
    exact OrderEmbedding.coe_ofStrictMono _
  have hpE : (pE : Fin l → Fin m) = echelonLeadingColumn E := by
    dsimp [pE]
    exact OrderEmbedding.coe_ofStrictMono _
  have hrange : Set.range pD = Set.range pE := by
    rw [hpD, hpE]
    exact echelonLeadingColumn_range_eq_of_rowSpace_eq hDE
  have heq : pD = pE := (OrderEmbedding.range_eq_iff).mp hrange
  funext i
  have hi := DFunLike.congr_fun heq i
  rw [hpD, hpE] at hi
  exact hi

theorem echelon_pivotColumn_apply {l m : ℕ}
    (D : EchelonMatrix K l m) (i j : Fin l) :
    D.1 j (echelonLeadingColumn D i) = if j = i then 1 else 0 := by
  split_ifs with hji
  · subst j
    exact D.2.1.eq_one (echelonLeadingColumn_isLeadingEntry D i)
  · exact D.2.1.eq_zero_of_ne_of_isLeadingEntry hji
      (echelonLeadingColumn_isLeadingEntry D i)

theorem echelonMatrix_eq_of_rowSpace_eq
    {l m : ℕ} {D E : EchelonMatrix K l m}
    (hDE : echelonRowSpace D = echelonRowSpace E) : D.1 = E.1 := by
  have hp : echelonLeadingColumn D = echelonLeadingColumn E :=
    echelonLeadingColumn_eq_of_rowSpace_eq hDE
  have hspan : Submodule.span K (Set.range D.1.row) =
      Submodule.span K (Set.range E.1.row) := congrArg Subtype.val hDE
  ext i j
  have hxi : D.1.row i ∈ Submodule.span K (Set.range E.1.row) := by
    have hxi' : D.1.row i ∈ Submodule.span K (Set.range D.1.row) :=
      Submodule.subset_span ⟨i, rfl⟩
    rw [hspan] at hxi'
    exact hxi'
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hxi
  have hcoeff (r : Fin l) : c r = if i = r then 1 else 0 := by
    have hsum : ∑ q : Fin l, c q * (E.1 : M l m K) q
          (echelonLeadingColumn E r) = c r := by
      rw [Finset.sum_eq_single r]
      · simp [echelon_pivotColumn_apply]
      · intro q hq hqr
        simp [echelon_pivotColumn_apply E r q, hqr]
      · simp
    have heval : ∑ q : Fin l, c q * (E.1 : M l m K) q
          (echelonLeadingColumn E r) =
        D.1 i (echelonLeadingColumn D r) := by
      have hcr := congrFun hc (echelonLeadingColumn E r)
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply,
        hp] using hcr
    rw [← hsum, heval, echelon_pivotColumn_apply]
  have hrow : D.1.row i = E.1.row i := by
    rw [← hc]
    ext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · simp [hcoeff]
    · intro q hq hqi
      have hcq : c q = 0 := by simp [hcoeff, hqi, Ne.symm hqi]
      simp [hcq]
    · simp
  exact congrFun hrow j

/- The manuscript's direct definition
   `Λ_D = (M_{1 × l}(K) D) ∩ O_K^m` (equation `eq:defi_of_lambda`).
   We keep this carrier written in terms of the rows of `D`; the equality with
   the row-space-indexed module is proved below rather than hidden in the
   definition. -/
def echelonLambda {l m : ℕ} (D : EchelonMatrix K l m) :
    Submodule (𝓞 K) (Fin m → 𝓞 K) where
  carrier := {v | (fun j => (v j : K)) ∈
    Submodule.span K (Set.range D.1.row)}
  zero_mem' := by
    change (0 : Fin m → K) ∈ Submodule.span K (Set.range D.1.row)
    exact Submodule.zero_mem _
  add_mem' := by
    intro x y hx hy
    change (fun j => (x j : K)) ∈
      Submodule.span K (Set.range D.1.row) at hx
    change (fun j => (y j : K)) ∈
      Submodule.span K (Set.range D.1.row) at hy
    change (fun j => ((x + y) j : K)) ∈
      Submodule.span K (Set.range D.1.row)
    convert Submodule.add_mem (Submodule.span K (Set.range D.1.row)) hx hy
      using 1
    ext j
    simp
  smul_mem' := by
    intro a x hx
    change (fun j => (x j : K)) ∈
      Submodule.span K (Set.range D.1.row) at hx
    change (fun j => ((a • x) j : K)) ∈
      Submodule.span K (Set.range D.1.row)
    convert Submodule.smul_mem (Submodule.span K (Set.range D.1.row))
      (a : K) hx using 1
    ext j
    simp [Pi.smul_apply]

@[simp]
theorem mem_echelonLambda_iff {l m : ℕ} (D : EchelonMatrix K l m)
    (v : Fin m → 𝓞 K) :
    v ∈ echelonLambda D ↔
      (fun j => (v j : K)) ∈ Submodule.span K (Set.range D.1.row) := Iff.rfl

theorem echelonLambda_eq_integralRowModule {l m : ℕ}
    (D : EchelonMatrix K l m) :
    echelonLambda D = integralRowModule (echelonRowSpace D) := by
  apply Submodule.ext
  intro v
  rfl

/- [derived consequence, paper equation `eq:defi_of_lambda`, lines 760--795]
   Inclusion of the primitive lattices attached to two echelon representatives
   is equivalent to inclusion of their rational row spaces.  This is the
   bridge needed to translate the paper's `Λ_{D'} ⊆ Λ_D` condition into the
   row-space indexing used by the counting development. -/
theorem echelonLambda_le_iff_echelonRowSpace_le
    {l l' m : ℕ} (D : EchelonMatrix K l m) (D' : EchelonMatrix K l' m) :
    echelonLambda D' ≤ echelonLambda D ↔
      (echelonRowSpace D').1 ≤ (echelonRowSpace D).1 := by
  constructor
  · intro h x hx
    let x' : (echelonRowSpace D').1 := ⟨x, hx⟩
    have hspan : Submodule.span K
        (Set.range (fun w : integralRowModule (echelonRowSpace D') =>
          (integralRowToRowSpace (echelonRowSpace D') w :
            (echelonRowSpace D').1))) = ⊤ :=
      span_range_integralRowToRowSpace (echelonRowSpace D')
    have hxspan : x' ∈ Submodule.span K
        (Set.range (fun w : integralRowModule (echelonRowSpace D') =>
          (integralRowToRowSpace (echelonRowSpace D') w :
            (echelonRowSpace D').1))) := by
      rw [hspan]
      trivial
    refine Submodule.span_induction (p := fun x : (echelonRowSpace D').1 =>
      fun _ => x.1 ∈ (echelonRowSpace D).1) ?_ ?_ ?_ ?_ hxspan
    · rintro _ ⟨w, rfl⟩
      have hw : w.1 ∈ echelonLambda D' := by
        rw [echelonLambda_eq_integralRowModule]
        exact w.2
      change (fun j => (w.1 j : K)) ∈
        Submodule.span K (Set.range D.1.row)
      exact (mem_echelonLambda_iff D w.1).mp (h hw)
    · exact (echelonRowSpace D).1.zero_mem
    · intro x y _ _ hx hy
      exact (echelonRowSpace D).1.add_mem hx hy
    · intro c x _ hx
      exact (echelonRowSpace D).1.smul_mem c hx
  · intro h v hv
    apply (mem_echelonLambda_iff D v).mpr
    exact h ((mem_echelonLambda_iff D' v).mp hv)

/- The denominator module from equation `de:denonimator` (line 193).  Its
   elements are the coefficient vectors `v ∈ O_K^l` for which the row
   combination `vᵀ D` has integral coordinates. -/
def echelonDenominatorModule {l m : ℕ} (D : EchelonMatrix K l m) :
    Submodule (𝓞 K) (Fin l → 𝓞 K) where
  carrier := {v | ∃ w : Fin m → 𝓞 K, ∀ j,
    (w j : K) = ∑ i : Fin l, (v i : K) * (D.1 : M l m K) i j}
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro j
    simp
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨wx, hx⟩
    rcases hy with ⟨wy, hy⟩
    refine ⟨wx + wy, ?_⟩
    intro j
    simp only [Pi.add_apply, RingHom.map_add, add_mul]
    rw [Finset.sum_add_distrib]
    change (wx j : K) + (wy j : K) = _
    rw [hx j, hy j]
  smul_mem' := by
    intro a x hx
    rcases hx with ⟨w, hx⟩
    refine ⟨a • w, ?_⟩
    intro j
    calc
      ((a • w) j : K) = (a : K) * (w j : K) := by
        simp [Pi.smul_apply, Algebra.smul_def]
      _ = (a : K) * ∑ i : Fin l,
          (x i : K) * (D.1 : M l m K) i j := by rw [hx j]
      _ = ∑ i : Fin l, (a : K) *
          ((x i : K) * (D.1 : M l m K) i j) := by
        rw [Finset.mul_sum]
      _ = ∑ i : Fin l, ((a • x) i : K) *
          (D.1 : M l m K) i j := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Pi.smul_apply, Algebra.smul_def]
        ring

@[simp]
theorem mem_echelonDenominatorModule_iff {l m : ℕ}
    (D : EchelonMatrix K l m) (v : Fin l → 𝓞 K) :
    v ∈ echelonDenominatorModule D ↔
      ∃ w : Fin m → 𝓞 K, ∀ j,
        (w j : K) = ∑ i : Fin l, (v i : K) * (D.1 : M l m K) i j := Iff.rfl

/- The reduced-row-echelon pivots make the coefficient vector integral again:
   an integral vector in the row space has integral coordinates at the pivot
   columns.  This is the algebraic point needed to identify `Λ_D` with the
   image of the denominator module. -/
theorem mem_echelonLambda_iff_exists_integral_coeff
    {l m : ℕ} (D : EchelonMatrix K l m) (v : Fin m → 𝓞 K) :
    v ∈ echelonLambda D ↔
      ∃ c : Fin l → 𝓞 K, ∀ j,
        (v j : K) = ∑ i : Fin l, (c i : K) *
          (D.1 : M l m K) i j := by
  constructor
  · intro hv
    have hv' : (fun j => (v j : K)) ∈
        Submodule.span K (Set.range D.1.row) := hv
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun K).mp hv'
    let lead : Fin l → Fin m := fun i =>
      (exists_echelon_leadingEntry D i).choose
    have hlead (i : Fin l) : D.1.IsLeadingEntry i (lead i) :=
      (exists_echelon_leadingEntry D i).choose_spec
    have hzero (i i' : Fin l) (hne : i' ≠ i) :
        (D.1 : M l m K) i' (lead i) = 0 := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact D.2.1.eq_zero hlt (hlead i)
      · exact D.2.1.isRowEchelon hgt (hlead i).1
    have hcoeff (i : Fin l) : c i = (v (lead i) : K) := by
      have hcj : ∑ x : Fin l, c x *
          (D.1 : M l m K) x (lead i) = (v (lead i) : K) := by
        simpa [Pi.smul_apply] using congrFun hc (lead i)
      have hsum : ∑ x : Fin l, c x *
          (D.1 : M l m K) x (lead i) = c i := by
        rw [Finset.sum_eq_single i]
        · simp [D.2.1.eq_one (hlead i)]
        · intro b hb hbi
          rw [hzero i b hbi, mul_zero]
        · simp
      exact hsum.symm.trans hcj
    refine ⟨fun i => v (lead i), ?_⟩
    intro j
    have hc' := congrFun hc j
    calc
      (v j : K) = ∑ i : Fin l, c i *
          (D.1 : M l m K) i j := by
            simpa [Pi.smul_apply] using hc'.symm
      _ = ∑ i : Fin l, ((v (lead i) : 𝓞 K) : K) *
          (D.1 : M l m K) i j := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hcoeff]
  · rintro ⟨c, hc⟩
    change (fun j => (v j : K)) ∈ Submodule.span K (Set.range D.1.row)
    rw [Submodule.mem_span_range_iff_exists_fun K]
    refine ⟨fun i => (c i : K), ?_⟩
    ext j
    rw [Finset.sum_apply]
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.row_apply] using (hc j).symm

theorem mem_echelonLambda_iff_exists_denominator_coeff
    {l m : ℕ} (D : EchelonMatrix K l m) (v : Fin m → 𝓞 K) :
    v ∈ echelonLambda D ↔
      ∃ c : echelonDenominatorModule D, ∀ j,
        (v j : K) = ∑ i : Fin l, (c.1 i : K) *
          (D.1 : M l m K) i j := by
  constructor
  · intro hv
    obtain ⟨c, hc⟩ := mem_echelonLambda_iff_exists_integral_coeff D v |>.mp hv
    have hcmem : c ∈ echelonDenominatorModule D := by
      exact ⟨v, hc⟩
    exact ⟨⟨c, hcmem⟩, hc⟩
  · rintro ⟨c, hc⟩
    exact mem_echelonLambda_iff_exists_integral_coeff D v |>.mpr
      ⟨c.1, hc⟩

/- Every finite family of coefficients of `D` has a common nonzero integral
   multiple.  Consequently the denominator module contains a full scalar
   multiple of `𝓞_K^l`; this is the elementary finiteness input behind the
   paper's denominator index. -/
theorem exists_nonzero_scalar_mem_echelonDenominatorModule
    {l m : ℕ} (D : EchelonMatrix K l m) :
    ∃ a : 𝓞 K, a ≠ 0 ∧
      ∀ v : Fin l → 𝓞 K,
        a • v ∈ echelonDenominatorModule D := by
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      (R := 𝓞 K) (S := K) (nonZeroDivisors (𝓞 K))
      (fun p : Fin l × Fin m => (D.1 : M l m K) p.1 p.2)
  let q : Fin l × Fin m → 𝓞 K := fun p => (hb p).choose
  have hq (p : Fin l × Fin m) :
      (q p : K) = (b.1 : K) * (D.1 : M l m K) p.1 p.2 := by
    simpa [q, IsLocalization.IsInteger, Algebra.smul_def] using
      (hb p).choose_spec
  have hb0 : b.1 ≠ 0 := nonZeroDivisors.coe_ne_zero b
  refine ⟨b.1, hb0, ?_⟩
  intro v
  refine ⟨fun j => ∑ i : Fin l, v i * q (i, j), ?_⟩
  intro j
  calc
    ((∑ i : Fin l, v i * q (i, j) : 𝓞 K) : K) =
        ∑ i : Fin l, (v i : K) * (q (i, j) : K) := by simp
    _ = ∑ i : Fin l, (v i : K) *
        ((b.1 : K) * (D.1 : M l m K) i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hq (i, j)]
    _ = ∑ i : Fin l, ((b.1 • v) i : K) *
        (D.1 : M l m K) i j := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Pi.smul_apply, Algebra.smul_def]
      ring

/- The paper's integer index `[O_K^l : ...]`.  `AddSubgroup.index` is zero
   precisely in the infinite-index case, so the finiteness/positivity needed
   later remains an explicit theorem obligation rather than an implicit
   assumption. -/
noncomputable def echelonDenominator {l m : ℕ}
    (D : EchelonMatrix K l m) : ℕ :=
  (echelonDenominatorModule D).toAddSubgroup.index

/- The coefficient module for `n` rows is the product of `n` copies of the
   one-row denominator module.  This is the product-index calculation that
   produces the exponent `n` in equation `eq:denominator_index`. -/
def echelonDenominatorMatrixModule {l m n : ℕ}
    (D : EchelonMatrix K l m) :
    Submodule (𝓞 K) (Fin n → Fin l → 𝓞 K) where
  carrier := {C | ∀ i, C i ∈ echelonDenominatorModule D}
  zero_mem' := by
    intro i
    exact (echelonDenominatorModule D).zero_mem
  add_mem' := by
    intro C C' hC hC' i
    exact (echelonDenominatorModule D).add_mem (hC i) (hC' i)
  smul_mem' := by
    intro a C hC i
    exact (echelonDenominatorModule D).smul_mem a (hC i)

theorem echelonDenominatorMatrixModule_index
    {l m n : ℕ} (D : EchelonMatrix K l m) :
    (echelonDenominatorMatrixModule (n := n) D).toAddSubgroup.index =
      echelonDenominator D ^ n := by
  have hmodule : (echelonDenominatorMatrixModule (n := n) D).toAddSubgroup =
      AddSubgroup.pi Set.univ
        (fun _ : Fin n => (echelonDenominatorModule D).toAddSubgroup) := by
    ext C
    change (∀ i, C i ∈ echelonDenominatorModule D) ↔
      ∀ i ∈ (Set.univ : Set (Fin n)),
        C i ∈ (echelonDenominatorModule D).toAddSubgroup
    simp
  rw [hmodule, AddSubgroup.index_pi]
  simp [echelonDenominator, Finset.prod_const]

theorem echelonDenominatorModule_finiteIndex
    {l m : ℕ} (D : EchelonMatrix K l m) :
    (echelonDenominatorModule D).toAddSubgroup.FiniteIndex := by
  obtain ⟨a, ha, ha_mem⟩ :=
    exists_nonzero_scalar_mem_echelonDenominatorModule D
  let I : Ideal (𝓞 K) := Ideal.span ({a} : Set (𝓞 K))
  have hI : I ≠ ⊥ := by
    intro hI
    have ha' : a ∈ I := by
      exact Ideal.mem_span_singleton_self a
    apply ha
    simpa [I, hI] using ha'
  letI : Finite (𝓞 K ⧸ I) :=
    Ideal.finiteQuotientOfFreeOfNeBot I hI
  let H : Submodule (𝓞 K) (Fin l → 𝓞 K) :=
    I • (⊤ : Submodule (𝓞 K) (Fin l → 𝓞 K))
  have hHquot : Finite ((Fin l → 𝓞 K) ⧸ H) := by
    dsimp [H]
    exact Submodule.finite_quotient_smul I (N := ⊤) Module.Finite.fg_top
  have hHindex : H.toAddSubgroup.FiniteIndex := by
    letI : Finite ((Fin l → 𝓞 K) ⧸ H.toAddSubgroup) := by
      change Finite ((Fin l → 𝓞 K) ⧸ H)
      exact hHquot
    exact AddSubgroup.finiteIndex_of_finite_quotient
  letI : H.toAddSubgroup.FiniteIndex := hHindex
  have hHN : H.toAddSubgroup ≤
      (echelonDenominatorModule D).toAddSubgroup := by
    intro v hv
    change v ∈ echelonDenominatorModule D
    have hsub : H ≤ echelonDenominatorModule D := by
      dsimp [H]
      refine Submodule.smul_le.mpr ?_
      intro r hr x hx
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hr
      rw [← hs, mul_smul]
      exact (echelonDenominatorModule D).smul_mem s (ha_mem x)
    exact hsub hv
  exact AddSubgroup.finiteIndex_of_le hHN

theorem echelonDenominator_ne_zero
    {l m : ℕ} (D : EchelonMatrix K l m) :
    echelonDenominator D ≠ 0 := by
  exact (echelonDenominatorModule_finiteIndex D).index_ne_zero

theorem echelonDenominator_pos
    {l m : ℕ} (D : EchelonMatrix K l m) :
    0 < echelonDenominator D :=
  Nat.pos_of_ne_zero (echelonDenominator_ne_zero D)

/- The coefficient-to-row map appearing in the paper's
   `M_{1 × l}(K) D`.  It is written explicitly so that the ambient target is
   the row space over `K`, while the denominator module remains a subgroup of
   `𝓞_K^l`. -/
noncomputable def echelonRowCombinationLinearMap
    {l m : ℕ} (D : EchelonMatrix K l m) :
    (Fin l → K) →ₗ[K] (Fin m → K) where
  toFun c := fun j => ∑ i : Fin l, c i * (D.1 : M l m K) i j
  map_add' c c' := by
    ext j
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    rw [Finset.mul_sum]

@[simp]
theorem echelonRowCombinationLinearMap_apply
    {l m : ℕ} (D : EchelonMatrix K l m)
    (c : Fin l → K) (j : Fin m) :
    echelonRowCombinationLinearMap D c j =
      ∑ i : Fin l, c i * (D.1 : M l m K) i j := rfl

theorem echelonRowCombinationLinearMap_injective
    {l m : ℕ} (D : EchelonMatrix K l m) :
    Function.Injective (echelonRowCombinationLinearMap D) := by
  intro c c' hcc'
  apply (echelon_rows_linearIndependent D).fintypeLinearCombination_injective
  funext j
  have hj := congrFun hcc' j
  simpa [Fintype.linearCombination_apply, Matrix.row_apply, smul_eq_mul]
    using hj

/- Restriction of the preceding map to integral coefficients.  Its image is
   the coefficient lattice `𝓞_K^l D`, and its denominator-module image is
   exactly `M_1(Λ_D)`. -/
def echelonRowCombinationAddHom
    {l m : ℕ} (D : EchelonMatrix K l m) :
    (Fin l → 𝓞 K) →+ (Fin m → K) where
  toFun c := fun j => ∑ i : Fin l, (c i : K) * (D.1 : M l m K) i j
  map_zero' := by
    ext j
    simp
  map_add' c c' := by
    ext j
    simp only [Pi.add_apply, RingHom.map_add, add_mul, Finset.sum_add_distrib]

@[simp]
theorem echelonRowCombinationAddHom_apply
    {l m : ℕ} (D : EchelonMatrix K l m)
    (c : Fin l → 𝓞 K) (j : Fin m) :
    echelonRowCombinationAddHom D c j =
      ∑ i : Fin l, (c i : K) * (D.1 : M l m K) i j := rfl

theorem echelonRowCombinationAddHom_injective
    {l m : ℕ} (D : EchelonMatrix K l m) :
    Function.Injective (echelonRowCombinationAddHom D) := by
  intro c c' hcc'
  have hcoeff : (fun i => (c i : K)) = (fun i => (c' i : K)) := by
    apply echelonRowCombinationLinearMap_injective D
    funext j
    exact congrFun hcc' j
  funext i
  apply NumberField.RingOfIntegers.coe_injective
  exact congrFun hcoeff i

theorem echelonDenominator_relIndex_rowImage
    {l m : ℕ} (D : EchelonMatrix K l m) :
    ((echelonDenominatorModule D).toAddSubgroup.map
          (echelonRowCombinationAddHom D)).relIndex
        (echelonRowCombinationAddHom D).range =
      echelonDenominator D := by
  rw [(echelonRowCombinationAddHom D).range_eq_map]
  rw [AddSubgroup.relIndex_map_map_of_injective
    (echelonDenominatorModule D).toAddSubgroup ⊤
    (echelonRowCombinationAddHom_injective D)]
  simp [echelonDenominator]

/- The integral form of the paper's `M_n(Λ_D)`: matrices whose rows lie in
   the direct module `echelonLambda D`.  The ambient real matrix version is
   obtained by applying `embedMatrix`; this is the representation used by the
   Riemann-sum development. -/
def echelonIntegralRowMatrixModule {l m : ℕ}
    (D : EchelonMatrix K l m) (n : ℕ) :
    Submodule (𝓞 K) (IntegralMatrix K n m) where
  carrier := {A | ∀ i, A.row i ∈ echelonLambda D}
  zero_mem' := by
    intro i
    exact (echelonLambda D).zero_mem
  add_mem' := by
    intro A B hA hB i
    exact (echelonLambda D).add_mem (hA i) (hB i)
  smul_mem' := by
    intro a A hA i
    exact (echelonLambda D).smul_mem a (hA i)

@[simp]
theorem mem_echelonIntegralRowMatrixModule_iff {l m n : ℕ}
    (D : EchelonMatrix K l m) (A : IntegralMatrix K n m) :
    A ∈ echelonIntegralRowMatrixModule D n ↔
      ∀ i, A.row i ∈ echelonLambda D := Iff.rfl

/- The rowwise coefficient map for `M_{n × l}(𝓞_K) D`.  Its source is kept
   as an iterated function type so that the product index is the literal
   product of the one-row indices proved above. -/
def echelonMatrixCombinationAddHom
    {l m n : ℕ} (D : EchelonMatrix K l m) :
    (Fin n → Fin l → 𝓞 K) →+ (Fin n → Fin m → K) where
  toFun C := fun r => echelonRowCombinationAddHom D (C r)
  map_zero' := by
    funext r j
    simp
  map_add' C C' := by
    funext r j
    simp [Pi.add_apply, Finset.sum_add_distrib, add_mul]

@[simp]
theorem echelonMatrixCombinationAddHom_apply
    {l m n : ℕ} (D : EchelonMatrix K l m)
    (C : Fin n → Fin l → 𝓞 K) (r : Fin n) (j : Fin m) :
    echelonMatrixCombinationAddHom D C r j =
      ∑ i : Fin l, (C r i : K) * (D.1 : M l m K) i j := rfl

theorem echelonMatrixCombinationAddHom_injective
    {l m n : ℕ} (D : EchelonMatrix K l m) :
    Function.Injective (echelonMatrixCombinationAddHom (n := n) D) := by
  intro C C' hCC'
  funext r
  apply echelonRowCombinationAddHom_injective D
  exact congrFun hCC' r

/- The integral matrix viewed in the rational ambient matrix space. -/
def integralMatrixToKAddHom {n m : ℕ} (K : Type*) [Field K] [NumberField K] :
    IntegralMatrix K n m →+ (Fin n → Fin m → K) where
  toFun A := fun i j => (A i j : K)
  map_zero' := by
    funext i j
    simp
  map_add' A B := by
    funext i j
    simp

@[simp]
theorem integralMatrixToKAddHom_apply
    {n m : ℕ} (A : IntegralMatrix K n m) (i : Fin n) (j : Fin m) :
    integralMatrixToKAddHom K A i j = (A i j : K) := rfl

/- The image of the direct module `M_n(Λ_D)` in the same rational ambient
   group as the coefficient image. -/
def echelonIntegralMatrixKImage
    {l m n : ℕ} (D : EchelonMatrix K l m) :
    AddSubgroup (Fin n → Fin m → K) :=
  (echelonIntegralRowMatrixModule D n).toAddSubgroup.map
    (integralMatrixToKAddHom K)

theorem echelonDenominatorMatrixModule_map_eq_integralMatrixKImage
    {l m n : ℕ} (D : EchelonMatrix K l m) :
    (echelonDenominatorMatrixModule (n := n) D).toAddSubgroup.map
        (echelonMatrixCombinationAddHom (n := n) D) =
      echelonIntegralMatrixKImage (n := n) D := by
  ext A
  constructor
  · intro hA
    obtain ⟨C, hC, hCA⟩ := AddSubgroup.mem_map.mp hA
    change ∀ i, C i ∈ echelonDenominatorModule D at hC
    choose w hw using fun i =>
      (mem_echelonDenominatorModule_iff D (C i)).mp (hC i)
    let B : IntegralMatrix K n m := fun i j => w i j
    have hB : B ∈ echelonIntegralRowMatrixModule D n := by
      intro i
      apply (mem_echelonLambda_iff_exists_denominator_coeff D (w i)).2
      exact ⟨⟨C i, hC i⟩, hw i⟩
    refine AddSubgroup.mem_map.mpr ⟨B, hB, ?_⟩
    funext i j
    calc
      integralMatrixToKAddHom K B i j = (w i j : K) := rfl
      _ = ∑ q : Fin l, (C i q : K) * (D.1 : M l m K) q j := hw i j
      _ = echelonMatrixCombinationAddHom D C i j := rfl
      _ = A i j := congrFun (congrFun hCA i) j
  · intro hA
    obtain ⟨B, hB, hBA⟩ := AddSubgroup.mem_map.mp hA
    choose C hC using fun i =>
      (mem_echelonLambda_iff_exists_denominator_coeff D (B.row i)).mp
        (hB i)
    let C₀ : Fin n → Fin l → 𝓞 K := fun i => (C i).1
    have hC₀ : C₀ ∈ echelonDenominatorMatrixModule (n := n) D := by
      intro i
      exact (C i).2
    refine AddSubgroup.mem_map.mpr ⟨C₀, hC₀, ?_⟩
    funext i j
    calc
      echelonMatrixCombinationAddHom D C₀ i j =
          ∑ q : Fin l, (C₀ i q : K) * (D.1 : M l m K) q j := rfl
      _ = (B.row i j : K) := (hC i) j |>.symm
      _ = integralMatrixToKAddHom K B i j := rfl
      _ = A i j := congrFun (congrFun hBA i) j

theorem echelonDenominator_relIndex_matrixImage
    {l m n : ℕ} (D : EchelonMatrix K l m) :
    ((echelonDenominatorMatrixModule (n := n) D).toAddSubgroup.map
        (echelonMatrixCombinationAddHom (n := n) D)).relIndex
      (echelonMatrixCombinationAddHom (n := n) D).range =
      echelonDenominator D ^ n := by
  rw [(echelonMatrixCombinationAddHom (n := n) D).range_eq_map]
  rw [AddSubgroup.relIndex_map_map_of_injective
    (echelonDenominatorMatrixModule (n := n) D).toAddSubgroup ⊤
    (echelonMatrixCombinationAddHom_injective (n := n) D)]
  simpa [echelonDenominator] using echelonDenominatorMatrixModule_index D

/- This is the paper's equation (21), with both sides realized as additive
   subgroups of the same ambient `K`-matrix space. -/
theorem echelonDenominator_index_eq_paper
    {l m n : ℕ} (D : EchelonMatrix K l m) :
    (echelonIntegralMatrixKImage (n := n) D).relIndex
      (echelonMatrixCombinationAddHom (n := n) D).range =
      echelonDenominator D ^ n := by
  rw [← echelonDenominatorMatrixModule_map_eq_integralMatrixKImage D]
  exact echelonDenominator_relIndex_matrixImage D

theorem echelonIntegralRowMatrixModule_eq {l m n : ℕ}
    (D : EchelonMatrix K l m) :
    echelonIntegralRowMatrixModule D n =
      integralRowMatrixModule (echelonRowSpace D) n := by
  apply Submodule.ext
  intro A
  rfl

abbrev echelonIntegralMatrices {l m n : ℕ} (D : EchelonMatrix K l m) :=
  {A : IntegralMatrix K n m // A ∈ echelonIntegralRowMatrixModule D n}

noncomputable def echelonIntegralMatricesEquivIntegralRowMatrices
    {l m n : ℕ} (D : EchelonMatrix K l m) :
    echelonIntegralMatrices (n := n) D ≃
      {A : IntegralMatrix K n m //
        rowsInIntegralRowModule (echelonRowSpace D) A} := by
  apply Equiv.subtypeEquivProp
  funext A
  rw [echelonIntegralRowMatrixModule_eq D]
  rfl

@[simp]
theorem echelonIntegralMatricesEquivIntegralRowMatrices_val
    {l m n : ℕ} (D : EchelonMatrix K l m)
    (A : echelonIntegralMatrices (n := n) D) :
    (echelonIntegralMatricesEquivIntegralRowMatrices D A).1 = A.1 := rfl

theorem tsum_echelonIntegralMatrices_eq_integralRowMatrices
    {l m n : ℕ} (D : EchelonMatrix K l m)
    (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) :
    (∑' A : echelonIntegralMatrices (n := n) D,
      f (T⁻¹ • embedMatrix A.1)) =
      ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule (echelonRowSpace D) A},
        f (T⁻¹ • embedMatrix A.1) := by
  let e := echelonIntegralMatricesEquivIntegralRowMatrices (n := n) D
  let F : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule (echelonRowSpace D) A} → ℝ := fun A =>
    f (T⁻¹ • embedMatrix A.1)
  calc
    (∑' A : echelonIntegralMatrices (n := n) D,
        f (T⁻¹ • embedMatrix A.1)) =
        ∑' A : echelonIntegralMatrices (n := n) D, F (e A) := by
      apply tsum_congr
      intro A
      rfl
    _ = ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule (echelonRowSpace D) A}, F A := e.tsum_eq F
    _ = ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule (echelonRowSpace D) A},
        f (T⁻¹ • embedMatrix A.1) := by rfl

/- This is the real ambient version of the manuscript's notation `M_n(R)`
   from Definition `de:defi_of_M_t` (lines 1031--1036). -/
def echelonLambdaRealSet {l m : ℕ} (D : EchelonMatrix K l m) :
    Set (RowVector K m) :=
  (integralVectorEmbedding (K := K) m) ''
    (echelonLambda D : Set (Fin m → 𝓞 K))

def echelonMatrixSet {l m n : ℕ} (D : EchelonMatrix K l m) :
    Set (M n m (K_ℝ[K])) :=
  {A | ∀ i, rowVectorOfFun (A i) ∈ echelonLambdaRealSet D}

@[simp]
theorem mem_echelonMatrixSet_iff {l m n : ℕ}
    (D : EchelonMatrix K l m) (A : M n m (K_ℝ[K])) :
    A ∈ echelonMatrixSet D ↔
      ∀ i, rowVectorOfFun (A i) ∈ echelonLambdaRealSet D := Iff.rfl

/- Every real matrix in `M_n(Λ_D)` is the embedding of a unique integral
   matrix whose rows lie in the direct module.  This is the concrete bridge
   between the paper's set notation and the integral-matrix subtype used in
   the counting sums. -/
theorem mem_echelonMatrixSet_iff_exists_integralMatrix
    {l m n : ℕ} (D : EchelonMatrix K l m)
    (A : M n m (K_ℝ[K])) :
    A ∈ echelonMatrixSet D ↔
      ∃ B : IntegralMatrix K n m,
        B ∈ echelonIntegralRowMatrixModule D n ∧ embedMatrix B = A := by
  constructor
  · intro hA
    change ∀ i, rowVectorOfFun (A i) ∈ echelonLambdaRealSet D at hA
    choose v hv using hA
    let B : IntegralMatrix K n m := fun i => v i
    have hB : B ∈ echelonIntegralRowMatrixModule D n := by
      intro i
      exact (hv i).1
    have hBA : embedMatrix B = A := by
      ext i j
      exact congrFun (congrArg WithLp.ofLp (hv i).2) j
    exact ⟨B, hB, hBA⟩
  · rintro ⟨B, hB, rfl⟩
    intro i
    refine ⟨B.row i, hB i, ?_⟩
    apply PiLp.ext
    intro j
    rfl

/- The lattice used to represent `M_n(Λ_D)` after passing through the
   rational row space.  This is definitionally the current row-lattice model;
   the equality with the manuscript's direct definition
   `(M_{1×l}(K)D) ∩ O_K^m` is a separate algebraic bridge. -/
noncomputable abbrev echelonRowMatrixLattice {l m n : ℕ}
    (D : EchelonMatrix K l m) :=
  rowMatrixZLattice (echelonRowSpace D) n

/- The direct integral model of `M_n(Λ_D)` is equivalent to the row-space
   lattice used by the Riemann-sum lemmas.  The only proof input is the
   previously established equality of the two row modules. -/
noncomputable def echelonIntegralMatricesEquivRowMatrixZLattice
    {l m n : ℕ} (D : EchelonMatrix K l m) :
    echelonIntegralMatrices (n := n) D ≃
      echelonRowMatrixLattice (n := n) D := by
  have hp : (fun A : IntegralMatrix K n m =>
      A ∈ echelonIntegralRowMatrixModule D n) =
      (fun A : IntegralMatrix K n m =>
        rowsInIntegralRowModule (echelonRowSpace D) A) := by
    funext A
    rw [echelonIntegralRowMatrixModule_eq D]
    rfl
  let e₀ : echelonIntegralMatrices (n := n) D ≃
      {A : IntegralMatrix K n m //
        rowsInIntegralRowModule (echelonRowSpace D) A} :=
    Equiv.subtypeEquivProp hp
  exact e₀.trans
    (integralRowMatricesEquivRowMatrixZLattice (echelonRowSpace D) n)

@[simp]
theorem echelonIntegralMatricesEquivRowMatrixZLattice_coe
    {l m n : ℕ} (D : EchelonMatrix K l m)
    (A : echelonIntegralMatrices (n := n) D) :
    (((echelonIntegralMatricesEquivRowMatrixZLattice D A :
      echelonRowMatrixLattice D) :
        rowMatrixRealSpan (echelonRowSpace D) n) : M n m (K_ℝ[K])) =
      embedMatrix A.1 := by
  let e₀ : echelonIntegralMatrices (n := n) D ≃
      {A : IntegralMatrix K n m //
        rowsInIntegralRowModule (echelonRowSpace D) A} :=
    Equiv.subtypeEquivProp (by
      funext A
      rw [echelonIntegralRowMatrixModule_eq D]
      rfl)
  have h := integralRowMatricesEquivRowMatrixZLattice_coe
    (echelonRowSpace D) n (e₀ A)
  have hA0 : (e₀ A).1 = A.1 := rfl
  change (((integralRowMatricesEquivRowMatrixZLattice
      (echelonRowSpace D) n (e₀ A) :
      rowMatrixZLattice (echelonRowSpace D) n) :
        rowMatrixRealSpan (echelonRowSpace D) n) : M n m (K_ℝ[K])) =
      embedMatrix A.1
  simpa [hA0] using h

theorem echelonIntegralMatricesEquivRowMatrixZLattice_rank
    {l m n : ℕ} (D : EchelonMatrix K l m)
    (A : echelonIntegralMatrices (n := n) D) :
    rowMatrixRank (echelonRowSpace D)
        (echelonIntegralMatricesEquivRowMatrixZLattice D A) =
      integralMatrixRank A.1 := by
  let e₀ : echelonIntegralMatrices (n := n) D ≃
      {A : IntegralMatrix K n m //
        rowsInIntegralRowModule (echelonRowSpace D) A} :=
    echelonIntegralMatricesEquivIntegralRowMatrices (n := n) D
  let e₁ := integralRowMatricesEquivRowMatrixZLattice
    (echelonRowSpace D) n
  have he : e₁.symm
      (echelonIntegralMatricesEquivRowMatrixZLattice D A) = e₀ A := by
    change e₁.symm (e₁ (e₀ A)) = e₀ A
    exact e₁.symm_apply_apply _
  change integralMatrixRank
      (e₁.symm (echelonIntegralMatricesEquivRowMatrixZLattice D A)).1 =
    integralMatrixRank A.1
  rw [he]
  rfl

noncomputable def echelonIntegralMatricesRankEquivRowMatrixRank
    {l m n : ℕ} (D : EchelonMatrix K l m) :
    {A : echelonIntegralMatrices (n := n) D //
        integralMatrixRank A.1 = l} ≃
      {A : rowMatrixZLattice (echelonRowSpace D) n //
        rowMatrixRank (echelonRowSpace D) A = l} := {
  toFun := fun A => ⟨
    echelonIntegralMatricesEquivRowMatrixZLattice D A.1,
    (echelonIntegralMatricesEquivRowMatrixZLattice_rank D A.1).trans A.2⟩
  invFun := fun A => ⟨
    (echelonIntegralMatricesEquivRowMatrixZLattice (n := n) D).symm A.1,
    by
      have hrel := echelonIntegralMatricesEquivRowMatrixZLattice_rank
        (n := n) D ((echelonIntegralMatricesEquivRowMatrixZLattice
          (n := n) D).symm A.1)
      rw [(echelonIntegralMatricesEquivRowMatrixZLattice
        (n := n) D).apply_symm_apply] at hrel
      exact hrel.symm.trans A.2⟩
  left_inv := by
    intro A
    apply Subtype.ext
    exact (echelonIntegralMatricesEquivRowMatrixZLattice
      (n := n) D).left_inv A.1
  right_inv := by
    intro A
    apply Subtype.ext
    exact (echelonIntegralMatricesEquivRowMatrixZLattice
      (n := n) D).right_inv A.1 }

@[simp]
theorem echelonIntegralMatricesRankEquivRowMatrixRank_coe
    {l m n : ℕ} (D : EchelonMatrix K l m)
    (A : {A : echelonIntegralMatrices (n := n) D //
      integralMatrixRank A.1 = l}) :
    (((echelonIntegralMatricesRankEquivRowMatrixRank D A).1 :
      rowMatrixRealSpan (echelonRowSpace D) n) : M n m (K_ℝ[K])) =
      embedMatrix A.1.1 := by
  dsimp [echelonIntegralMatricesRankEquivRowMatrixRank]
  rw [echelonIntegralMatricesEquivRowMatrixZLattice_coe]

theorem tsum_echelonIntegralMatrices_rank_eq_rowMatrixZLattice_rank
    {l m n : ℕ} (D : EchelonMatrix K l m)
    (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) :
    (∑' A : {A : echelonIntegralMatrices (n := n) D //
        integralMatrixRank A.1 = l},
      f (T⁻¹ • embedMatrix A.1)) =
      ∑' A : {A : rowMatrixZLattice (echelonRowSpace D) n //
        rowMatrixRank (echelonRowSpace D) A = l},
      f (T⁻¹ • (((A.1 : rowMatrixRealSpan (echelonRowSpace D) n) :
        M n m (K_ℝ[K])))) := by
  let e := echelonIntegralMatricesRankEquivRowMatrixRank (n := n) D
  let F : {A : rowMatrixZLattice (echelonRowSpace D) n //
      rowMatrixRank (echelonRowSpace D) A = l} → ℝ := fun A =>
    f (T⁻¹ • (((A.1 : rowMatrixRealSpan (echelonRowSpace D) n) :
      M n m (K_ℝ[K]))))
  calc
    (∑' A : {A : echelonIntegralMatrices (n := n) D //
        integralMatrixRank A.1 = l},
        f (T⁻¹ • embedMatrix A.1)) =
        ∑' A : {A : echelonIntegralMatrices (n := n) D //
          integralMatrixRank A.1 = l}, F (e A) := by
      apply tsum_congr
      intro A
      dsimp [F, e]
      rw [echelonIntegralMatricesRankEquivRowMatrixRank_coe]
    _ = ∑' A : {A : rowMatrixZLattice (echelonRowSpace D) n //
        rowMatrixRank (echelonRowSpace D) A = l}, F A := e.tsum_eq F
    _ = ∑' A : {A : rowMatrixZLattice (echelonRowSpace D) n //
        rowMatrixRank (echelonRowSpace D) A = l},
        f (T⁻¹ • (((A.1 : rowMatrixRealSpan (echelonRowSpace D) n) :
          M n m (K_ℝ[K])))) := by rfl

/- [Lean infrastructure for paper equation `eq:defi_of_calF`, lines 784--803]
The row-space implementation of the paper's family
   `𝓕_l^(Csup)(T)` (equation `eq:defi_of_calF`).  The direct
   `Λ_D`-implementation and its equality with this definition are given
   below; keeping this representation is convenient for the existing lattice
   estimates. -/
noncomputable def calF {l m n : ℕ}
    (Csup T : ℝ) : Set (EchelonMatrix K l m) :=
  {D | ∃ A : echelonRowMatrixLattice D,
    rowMatrixRank (echelonRowSpace D) A = l ∧
      ‖((A.1 : rowMatrixRealSpan (echelonRowSpace D) n) :
        M n m (K_ℝ[K]))‖ ≤ Csup * T}

/- [paper, equation `eq:defi_of_calF`, lines 784--803] The manuscript
separately declares `𝓕_0(T) = {0}`.  We record that
   convention as a named family; the unique zero-row representative can be
   connected to `calF` after the zero-row echelon instance is developed. -/
def calFZero {m : ℕ} : Set (EchelonMatrix K 0 m) := Set.univ

def zeroEchelonMatrix {m : ℕ} : EchelonMatrix K 0 m :=
  ⟨0, by
    constructor
    · intro i₁ i₂ hlt
      exact Fin.elim0 i₁
    · intro i c hA
      exact Fin.elim0 i
    · intro i₁ i₂ c hlt hA
      exact Fin.elim0 i₁,
    by simp⟩

theorem calFZero_eq_singleton {m : ℕ} :
    calFZero (K := K) (m := m) = {zeroEchelonMatrix (K := K) (m := m)} := by
  ext D
  constructor
  · intro hD
    simp only [Set.mem_singleton_iff]
    apply Subtype.ext
    funext i j
    exact Fin.elim0 i
  · intro hD
    trivial

theorem echelonRowSpace_surjective_zero {m : ℕ} :
    Function.Surjective
      (echelonRowSpace (K := K) (l := 0) (m := m)) := by
  intro V
  have hV : V.1 = (⊥ : Submodule K (Fin m → K)) :=
    Submodule.finrank_eq_zero.mp V.2
  refine ⟨zeroEchelonMatrix (K := K) (m := m), ?_⟩
  apply Subtype.ext
  rw [hV]
  apply Submodule.ext
  intro x
  simp [echelonRowSpace, zeroEchelonMatrix]

theorem echelonRowSpace_surjective_one {m : ℕ} (V : Grassmannian K m 1) :
    ∃ D : EchelonMatrix K 1 m, echelonRowSpace D = V := by
  have hVne : V.1 ≠ ⊥ := by
    intro hV
    have : Module.finrank K V.1 = 0 := by
      rw [hV]
      simp
    exact one_ne_zero (V.2.symm.trans this)
  obtain ⟨x, hxV, hx0'⟩ := SetLike.exists_of_lt
    (show (⊥ : Submodule K (Fin m → K)) < V.1 by
      rw [bot_lt_iff_ne_bot]
      exact hVne)
  have hx0 : x ≠ 0 := by
    intro hx
    apply hx0'
    simpa [hx]
  obtain ⟨c, hc0, hcc⟩ :=
    wellFounded_lt.has_min {j : Fin m | x j ≠ 0} (Function.ne_iff.mp hx0)
  have hxc : ∀ j < c, x j = 0 := by
    intro j hj
    by_contra hj0
    exact (hcc j hj0) hj
  let A : Matrix (Fin 1) (Fin m) K := fun _ j => (x c)⁻¹ * x j
  have hAc : A 0 c = 1 := by
    dsimp [A]
    rw [inv_mul_cancel₀ hc0]
  have hAlead : A.IsLeadingEntry 0 c := by
    refine ⟨?_, ?_⟩
    · intro j hj
      simp [A, hxc j hj]
    · rw [hAc]
      exact one_ne_zero
  have hArref : A.IsReducedRowEchelon := by
    refine ⟨?_, ?_, ?_⟩
    · intro i₁ i₂ hlt
      omega
    · intro i c' hc'
      have hcc' : c' = c := (hc'.unique hAlead)
      subst c'
      exact hAc
    · intro i₁ i₂ c' hlt hc'
      omega
  have hAnonzero : A 0 ≠ 0 := hAlead.row_ne_zero
  have hrow0 : A.row 0 = A 0 := by
    funext j
    rfl
  have hspan : Submodule.span K (Set.range A.row) = K ∙ A 0 := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rw [hrow0]
      exact Submodule.mem_span_singleton.mpr ⟨1, by simp⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      rw [← hrow0]
      exact Submodule.subset_span ⟨0, rfl⟩
  have hArank : A.rank = 1 := by
    rw [Matrix.rank_eq_finrank_span_row, hspan, finrank_span_singleton hAnonzero]
  let D : EchelonMatrix K 1 m := ⟨A, hArref, hArank⟩
  refine ⟨D, ?_⟩
  apply Subtype.ext
  apply Submodule.eq_of_le_of_finrank_eq
  · intro y hy
    change y ∈ Submodule.span K (Set.range A.row) at hy
    rw [hspan] at hy
    rcases Submodule.mem_span_singleton.mp hy with ⟨a, rfl⟩
    change a • A 0 ∈ V.1
    apply V.1.smul_mem
    have hA0 : A 0 = (x c)⁻¹ • x := by
      funext j
      simp [A, Pi.smul_apply]
    rw [hA0]
    exact V.1.smul_mem _ hxV
  · change Module.finrank K (Submodule.span K (Set.range A.row)) = Module.finrank K V.1
    rw [hspan, finrank_span_singleton hAnonzero, V.2]

def zeroLiftMatrix {l m : ℕ} (A : Matrix (Fin l) (Fin m) K) :
    Matrix (Fin l) (Fin (m + 1)) K := fun i => Fin.cons 0 (A i)

theorem zeroLiftMatrix_leading_iff {l m : ℕ}
    (D : EchelonMatrix K l m) (i : Fin l) (c : Fin m) :
    (zeroLiftMatrix D.1).IsLeadingEntry i (Fin.succ c) ↔
      D.1.IsLeadingEntry i c := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j hj
      simpa [zeroLiftMatrix] using h.1 (Fin.succ j) (Fin.succ_lt_succ_iff.mpr hj)
    · simpa [zeroLiftMatrix] using h.2
  · intro h
    refine ⟨?_, ?_⟩
    · intro j hj
      cases j using Fin.cases with
      | zero => simp [zeroLiftMatrix]
      | succ j =>
          simpa [zeroLiftMatrix] using h.1 j (Fin.succ_lt_succ_iff.mp hj)
    · simpa [zeroLiftMatrix] using h.2

theorem zeroLiftMatrix_isReducedRowEchelon {l m : ℕ}
    (D : EchelonMatrix K l m) :
    (zeroLiftMatrix D.1).IsReducedRowEchelon := by
  refine ⟨?_, ?_, ?_⟩
  · intro i₁ i₂ hlt c₂ hc₂
    cases c₂ using Fin.cases with
    | zero => simp [zeroLiftMatrix]
    | succ c₂ =>
        apply D.2.1.isRowEchelon hlt
        intro c₁ hc₁
        simpa [zeroLiftMatrix] using hc₂ (Fin.succ c₁)
          (Fin.succ_lt_succ_iff.mpr hc₁)
  · intro i c' hc'
    have hc'0 : c' ≠ 0 := by
      intro hc'0
      subst c'
      simpa [zeroLiftMatrix] using hc'.2
    obtain ⟨c, hc⟩ := Fin.exists_succ_eq_of_ne_zero hc'0
    subst c'
    have htail := (zeroLiftMatrix_leading_iff D i c).mp hc'
    simpa [zeroLiftMatrix] using D.2.1.eq_one htail
  · intro i₁ i₂ c' hlt hc'
    have hc'0 : c' ≠ 0 := by
      intro hc'0
      subst c'
      simpa [zeroLiftMatrix] using hc'.2
    obtain ⟨c, hc⟩ := Fin.exists_succ_eq_of_ne_zero hc'0
    subst c'
    have htail := (zeroLiftMatrix_leading_iff D i₂ c).mp hc'
    simpa [zeroLiftMatrix] using D.2.1.eq_zero hlt htail

/- Lean infrastructure for the positive-rank existence induction.  These
   maps split a vector into its first coordinate and its tail; the branch
   below is the direct zero-first-coordinate construction. -/
noncomputable def echelonConsHead (m : ℕ) :
    (Fin (m + 1) → K) →ₗ[K] K :=
  (LinearMap.fst K K (Fin m → K)).comp
    (Fin.consLinearEquiv K (fun _ : Fin (m + 1) => K)).symm.toLinearMap

noncomputable def echelonConsTail (m : ℕ) :
    (Fin (m + 1) → K) →ₗ[K] (Fin m → K) :=
  (LinearMap.snd K K (Fin m → K)).comp
    (Fin.consLinearEquiv K (fun _ : Fin (m + 1) => K)).symm.toLinearMap

noncomputable def echelonConsZero (m : ℕ) :
    (Fin m → K) →ₗ[K] (Fin (m + 1) → K) :=
  (Fin.consLinearEquiv K (fun _ : Fin (m + 1) => K)).toLinearMap.comp
    (LinearMap.inr K K (Fin m → K))

theorem echelonConsHead_apply (m : ℕ) (v : Fin (m + 1) → K) :
    echelonConsHead m v = v 0 := by
  rfl

theorem echelonConsTail_apply (m : ℕ) (v : Fin (m + 1) → K) :
    echelonConsTail m v = Fin.tail v := by
  rfl

theorem echelonConsZero_apply (m : ℕ) (v : Fin m → K) :
    echelonConsZero m v = Fin.cons 0 v := by
  rfl

theorem echelonConsZero_tail_of_head_eq_zero (m : ℕ) (v : Fin (m + 1) → K)
    (hv : echelonConsHead m v = 0) :
    echelonConsZero m (echelonConsTail m v) = v := by
  funext i
  rw [echelonConsHead_apply] at hv
  rw [echelonConsZero_apply, echelonConsTail_apply]
  have hv' : Fin.cons 0 (Fin.tail v) = v := by
    rw [← Fin.cons_self_tail v]
    congr 1
    exact hv.symm
  exact congrFun hv' i

theorem echelonConsHead_range_eq_top_of_mem_ne_zero
    {l m : ℕ} (V : Grassmannian K (m + 1) l)
    (x : Fin (m + 1) → K) (hx : x ∈ V.1) (hx0 : x 0 ≠ 0) :
    LinearMap.range ((echelonConsHead m).comp V.1.subtype) =
      (⊤ : Submodule K K) := by
  rw [LinearMap.range_eq_top]
  intro y
  let f : V.1 →ₗ[K] K := (echelonConsHead m).comp V.1.subtype
  refine ⟨((x 0)⁻¹ * y) • ⟨x, hx⟩, ?_⟩
  change (echelonConsHead m) (((x 0)⁻¹ * y) • x) = y
  rw [map_smul, echelonConsHead_apply]
  rw [smul_eq_mul]
  calc
    (x 0)⁻¹ * y * x 0 = y * ((x 0)⁻¹ * x 0) := by ring
    _ = y := by rw [inv_mul_cancel₀ hx0, mul_one]

theorem echelonConsKernelTail_injective {l m : ℕ}
    (V : Grassmannian K (m + 1) l) :
    let f : V.1 →ₗ[K] K := (echelonConsHead m).comp V.1.subtype
    let g : V.1 →ₗ[K] (Fin m → K) := (echelonConsTail m).comp V.1.subtype
    Function.Injective (g.domRestrict (LinearMap.ker f)) := by
  dsimp
  intro v w hvw
  apply Subtype.ext
  have hp :
      (Fin.consLinearEquiv K (fun _ : Fin (m + 1) => K)).symm v.1.1 =
        (Fin.consLinearEquiv K (fun _ : Fin (m + 1) => K)).symm w.1.1 := by
    apply Prod.ext
    · change v.1.1 0 = w.1.1 0
      have hv : v.1.1 0 = 0 := by
        have hv' := LinearMap.mem_ker.mp v.2
        change v.1.1 0 = 0 at hv'
        exact hv'
      have hw : w.1.1 0 = 0 := by
        have hw' := LinearMap.mem_ker.mp w.2
        change w.1.1 0 = 0 at hw'
        exact hw'
      rw [hv, hw]
    · change Fin.tail v.1.1 = Fin.tail w.1.1
      simpa [echelonConsTail_apply] using hvw
  apply Subtype.ext
  exact (Fin.consLinearEquiv K (fun _ : Fin (m + 1) => K)).symm.injective hp

/- `derived consequence`/Lean infrastructure for Proposition `pr:trijection`:
   this is the zero-first-coordinate branch of the row-space induction. -/
theorem echelonRowSpace_surjective_of_head_zero
    {l m : ℕ} (V : Grassmannian K (m + 1) l)
    (hzero : ∀ v, v ∈ V.1 → v 0 = 0)
    (hsurj : Function.Surjective
      (echelonRowSpace (K := K) (l := l) (m := m))) :
    ∃ D : EchelonMatrix K l (m + 1), echelonRowSpace D = V := by
  let g : V.1 →ₗ[K] (Fin m → K) :=
    (echelonConsTail m).comp V.1.subtype
  have hg : Function.Injective g := by
    intro v w hvw
    apply Subtype.ext
    apply (Fin.consLinearEquiv K (fun _ : Fin (m + 1) => K)).symm.injective
    apply Prod.ext
    · change v.1 0 = w.1 0
      rw [hzero v.1 v.2, hzero w.1 w.2]
    · change Fin.tail v.1 = Fin.tail w.1
      simpa [g, echelonConsTail_apply] using hvw
  let W : Submodule K (Fin m → K) := g.range
  have hWfin : Module.finrank K W = l := by
    have he : V.1 ≃ₗ[K] W := LinearEquiv.ofInjective g hg
    exact he.finrank_eq.symm.trans V.2
  let Wg : Grassmannian K m l := ⟨W, hWfin⟩
  obtain ⟨D, hD⟩ := hsurj Wg
  let A : Matrix (Fin l) (Fin (m + 1)) K := zeroLiftMatrix D.1
  have hspanD : Submodule.span K (Set.range D.1.row) = W := by
    change (echelonRowSpace D).1 = W
    exact congrArg Subtype.val hD
  have hAV : Submodule.span K (Set.range A.row) ≤ V.1 := by
    rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    have hiW : D.1.row i ∈ W := by
      rw [← hspanD]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨v, hv⟩ := hiW
    have hvhead : v.1 0 = 0 := hzero v.1 v.2
    have hvEq : echelonConsZero m (echelonConsTail m v.1) = v.1 :=
      echelonConsZero_tail_of_head_eq_zero m v.1 (by
        simpa [echelonConsHead_apply] using hvhead)
    have hrow : A.row i = v.1 := by
      rw [show A.row i = echelonConsZero m (D.1.row i) by rfl]
      rw [← hv, ← hvEq]
      rfl
    rw [hrow]
    exact v.2
  have hVA : V.1 ≤ Submodule.span K (Set.range A.row) := by
    intro v hv
    have htailW : echelonConsTail m v ∈ W := by
      exact ⟨⟨v, hv⟩, rfl⟩
    rw [← hspanD] at htailW
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp htailW
    have htailEq (j : Fin m) :
        echelonConsTail m v j = ∑ i, c i * D.1 i j := by
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply]
        using (congrFun hc j).symm
    have hvhead : v 0 = 0 := hzero v hv
    have hvEq : echelonConsZero m (echelonConsTail m v) = v :=
      echelonConsZero_tail_of_head_eq_zero m v
        (by simpa [echelonConsHead_apply] using hvhead)
    have hsum : ∑ i, c i • A.row i ∈ Submodule.span K (Set.range A.row) := by
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [← hvEq]
    have hsumEq : echelonConsZero m (echelonConsTail m v) =
        ∑ i, c i • A.row i := by
      funext j
      cases j using Fin.cases with
      | zero => simp [echelonConsZero, echelonConsTail, A, zeroLiftMatrix,
          Matrix.row_apply]
      | succ j =>
          rw [echelonConsZero_apply, Fin.cons_succ, htailEq]
          simp [A, zeroLiftMatrix, echelonConsZero_apply]
    rw [hsumEq]
    exact hsum
  have hspan : Submodule.span K (Set.range A.row) = V.1 :=
    le_antisymm hAV hVA
  have hArank : A.rank = l := by
    rw [Matrix.rank_eq_finrank_span_row, hspan, V.2]
  let D' : EchelonMatrix K l (m + 1) :=
    ⟨A, zeroLiftMatrix_isReducedRowEchelon D, hArank⟩
  exact ⟨D', by
    apply Subtype.ext
    exact hspan⟩

/- This is the complementary branch of the row-space induction: the first
   coordinate projection is nonzero, so a normalized pivot row is added and
   the lower rows are lifted from the kernel. -/
theorem echelonRowSpace_surjective_of_head_ne_zero {l m : ℕ}
    (V : Grassmannian K (m + 1) l)
    (x : Fin (m + 1) → K) (hx : x ∈ V.1) (hx0 : x 0 ≠ 0)
    (hsurj : Function.Surjective
      (echelonRowSpace (K := K) (l := l - 1) (m := m))) (hl : 1 ≤ l) :
    ∃ D : EchelonMatrix K l (m + 1), echelonRowSpace D = V := by
  obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  simp only [Nat.succ_sub_one] at hsurj
  let f : V.1 →ₗ[K] K := (echelonConsHead m).comp V.1.subtype
  have hfrange : f.range = (⊤ : Submodule K K) := by
    simpa [f] using echelonConsHead_range_eq_top_of_mem_ne_zero V x hx hx0
  have hkerfin : Module.finrank K f.ker = l' := by
    have hsum := f.finrank_range_add_finrank_ker
    rw [hfrange, finrank_top, Module.finrank_self, V.2] at hsum
    omega
  let g : V.1 →ₗ[K] (Fin m → K) := (echelonConsTail m).comp V.1.subtype
  let gk : f.ker →ₗ[K] (Fin m → K) := g.domRestrict f.ker
  have hgk : Function.Injective gk := by
    simpa [f, g, gk] using echelonConsKernelTail_injective V
  let W : Submodule K (Fin m → K) := gk.range
  have hWfin : Module.finrank K W = l' := by
    have he : f.ker ≃ₗ[K] W := LinearEquiv.ofInjective gk hgk
    exact he.finrank_eq.symm.trans hkerfin
  let Wg : Grassmannian K m l' := ⟨W, hWfin⟩
  obtain ⟨D, hD⟩ := hsurj Wg
  let u : V.1 := (x 0)⁻¹ • ⟨x, hx⟩
  have huhead : (u : Fin (m + 1) → K) 0 = 1 := by
    change (x 0)⁻¹ * x 0 = 1
    exact inv_mul_cancel₀ hx0
  let lower : Fin l' → (Fin (m + 1) → K) := fun i =>
    echelonConsZero m (D.1.row i)
  let top : Fin (m + 1) → K :=
    (u : Fin (m + 1) → K) -
      ∑ i : Fin l',
        ((u : Fin (m + 1) → K) (Fin.succ (echelonLeadingColumn D i))) • lower i
  let A : Matrix (Fin (Nat.succ l')) (Fin (m + 1)) K := fun i =>
    Fin.cases top lower i
  have hspanD : Submodule.span K (Set.range D.1.row) = W := by
    change (echelonRowSpace D).1 = W
    exact congrArg Subtype.val hD
  have hlower : ∀ i : Fin l', lower i ∈ V.1 := by
    intro i
    have hiW : D.1.row i ∈ W := by
      rw [← hspanD]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨z, hz⟩ := hiW
    have hzhead : z.1.1 0 = 0 := by
      have := LinearMap.mem_ker.mp z.2
      change z.1.1 0 = 0 at this
      exact this
    have hzEq : echelonConsZero m (echelonConsTail m z.1.1) = z.1.1 :=
      echelonConsZero_tail_of_head_eq_zero m z.1.1 (by
        simpa [echelonConsHead_apply] using hzhead)
    have hztail : echelonConsTail m z.1.1 = D.1.row i := by
      simpa [gk, g, echelonConsTail_apply] using hz
    have hrowz : echelonConsZero m (D.1.row i) = z.1.1 := by
      rw [← hztail]
      exact hzEq
    rw [show lower i = echelonConsZero m (D.1.row i) by rfl, hrowz]
    exact z.1.2
  have htop_mem : top ∈ V.1 := by
    apply V.1.sub_mem (u.2)
    apply Submodule.sum_mem
    intro i hi
    exact V.1.smul_mem _ (hlower i)
  have htop_zero : top 0 = 1 := by
    dsimp [top]
    rw [show (u : Fin (m + 1) → K) 0 = 1 by exact huhead]
    simp [lower, echelonConsZero, echelonConsZero_apply]
  have htop_pivot (i : Fin l') :
      top (Fin.succ (echelonLeadingColumn D i)) = 0 := by
    have hlower_pivot (j : Fin l') :
        lower j (Fin.succ (echelonLeadingColumn D i)) = if j = i then 1 else 0 := by
      by_cases hji : j = i
      · subst j
        simp [lower, echelonConsZero, Matrix.row_apply,
          echelon_pivotColumn_apply]
      · have hp := echelon_pivotColumn_apply D i j
        simp [lower, echelonConsZero, Matrix.row_apply, hji, hp]
    have hterm (j : Fin l') :
        ((u : Fin (m + 1) → K) (Fin.succ (echelonLeadingColumn D j))) •
            lower j (Fin.succ (echelonLeadingColumn D i)) =
          if j = i then
            (u : Fin (m + 1) → K) (Fin.succ (echelonLeadingColumn D i)) else 0 := by
      rw [hlower_pivot]
      split_ifs with h
      · subst j
        simp [smul_eq_mul]
      · simp
    have hterm' (j : Fin l') :
        (((u : Fin (m + 1) → K) (Fin.succ (echelonLeadingColumn D j))) •
            lower j) (Fin.succ (echelonLeadingColumn D i)) =
          if j = i then
            (u : Fin (m + 1) → K) (Fin.succ (echelonLeadingColumn D i)) else 0 := by
      change (u : Fin (m + 1) → K) (Fin.succ (echelonLeadingColumn D j)) *
          lower j (Fin.succ (echelonLeadingColumn D i)) = _
      simpa [smul_eq_mul] using hterm j
    dsimp [top]
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · rw [hterm' i]
      simp [smul_eq_mul]
    · intro j hj hji
      rw [hterm' j]
      simp [hji]
    · simp
  have hlead_top : A.IsLeadingEntry 0 0 := by
    refine ⟨?_, ?_⟩
    · intro c hc
      exact False.elim ((not_lt_of_ge (Fin.zero_le c)) hc)
    · have hne : top 0 ≠ 0 := by
        rw [htop_zero]
        exact one_ne_zero
      simpa [A] using hne
  have hlead_lower (i : Fin l') :
      A.IsLeadingEntry (Fin.succ i) (Fin.succ (echelonLeadingColumn D i)) := by
    refine ⟨?_, ?_⟩
    · intro c hc
      cases c using Fin.cases with
      | zero =>
          simp [A, lower, echelonConsZero, Matrix.row_apply]
      | succ c =>
          have hc' : c < echelonLeadingColumn D i :=
            Fin.succ_lt_succ_iff.mp hc
          simpa [A, lower, echelonConsZero, Matrix.row_apply] using
            (echelonLeadingColumn_isLeadingEntry D i).1 c hc'
    · have hne : D.1 i (echelonLeadingColumn D i) ≠ 0 :=
        (echelonLeadingColumn_isLeadingEntry D i).2
      simpa [A, lower, echelonConsZero, Matrix.row_apply] using hne
  have hA : A.IsReducedRowEchelon := by
    refine ⟨?_, ?_, ?_⟩
    · intro i₁ i₂ hlt c hleft
      cases i₁ using Fin.cases with
      | zero =>
          cases i₂ using Fin.cases with
          | zero => omega
          | succ i₂ =>
              cases c using Fin.cases with
              | zero => simp [A, lower, echelonConsZero, Matrix.row_apply]
              | succ c =>
                  have hleft0 := hleft 0 (Fin.succ_pos c)
                  have htop0 : A 0 0 = 1 := by simpa [A] using htop_zero
                  rw [htop0] at hleft0
                  exact False.elim (one_ne_zero hleft0)
      | succ i₁ =>
          cases i₂ using Fin.cases with
          | zero => exact False.elim ((not_lt_of_ge (Fin.zero_le _)) hlt)
          | succ i₂ =>
              have hlt' : i₁ < i₂ := Fin.succ_lt_succ_iff.mp hlt
              cases c using Fin.cases with
              | zero => simp [A, lower, echelonConsZero, Matrix.row_apply]
              | succ c =>
                  have hleft' : ∀ j₁ < c, D.1 i₁ j₁ = 0 := by
                    intro j₁ hj₁
                    have h := hleft (Fin.succ j₁) (Fin.succ_lt_succ_iff.mpr hj₁)
                    simpa [A, lower, echelonConsZero, Matrix.row_apply] using h
                  have hz := D.2.1.isRowEchelon hlt' hleft'
                  simpa [A, lower, echelonConsZero, Matrix.row_apply] using hz
    · intro i c hc
      cases i using Fin.cases with
      | zero =>
          have hc0 : c = 0 := hc.unique hlead_top
          subst c
          simpa [A] using htop_zero
      | succ i =>
          have hc_eq : c = Fin.succ (echelonLeadingColumn D i) :=
            hc.unique (hlead_lower i)
          subst c
          simpa [A, lower, echelonConsZero, Matrix.row_apply] using
            D.2.1.eq_one (echelonLeadingColumn_isLeadingEntry D i)
    · intro i₁ i₂ c hlt hc
      cases i₁ using Fin.cases with
      | zero =>
          cases i₂ using Fin.cases with
          | zero => exact False.elim ((not_lt_of_ge (Fin.zero_le _)) hlt)
          | succ i₂ =>
              have hc_eq : c = Fin.succ (echelonLeadingColumn D i₂) :=
                hc.unique (hlead_lower i₂)
              subst c
              exact htop_pivot i₂
      | succ i₁ =>
          cases i₂ using Fin.cases with
          | zero => exact False.elim ((not_lt_of_ge (Fin.zero_le _)) hlt)
          | succ i₂ =>
              have hlt' : i₁ < i₂ := Fin.succ_lt_succ_iff.mp hlt
              cases c using Fin.cases with
              | zero =>
                  exact False.elim (hc.2 (by
                    simp [A, lower, echelonConsZero, Matrix.row_apply]))
              | succ c =>
                  have hDlead : D.1.IsLeadingEntry i₂ (echelonLeadingColumn D i₂) :=
                    echelonLeadingColumn_isLeadingEntry D i₂
                  have hDzero := D.2.1.eq_zero hlt' hDlead
                  have hc_eq : c = echelonLeadingColumn D i₂ := by
                    have hcD : D.1.IsLeadingEntry i₂ c := by
                      refine ⟨?_, ?_⟩
                      · intro j hj
                        have hj' := hc.1 (Fin.succ j) (Fin.succ_lt_succ_iff.mpr hj)
                        simpa [A, lower, echelonConsZero, Matrix.row_apply] using hj'
                      · simpa [A, lower, echelonConsZero, Matrix.row_apply] using hc.2
                    exact hcD.unique hDlead
                  subst c
                  simpa [A, lower, echelonConsZero, Matrix.row_apply] using hDzero
  have hAV : Submodule.span K (Set.range A.row) ≤ V.1 := by
    rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    cases i using Fin.cases with
    | zero =>
        change top ∈ V.1
        exact htop_mem
    | succ i =>
        change lower i ∈ V.1
        exact hlower i
  have hVA : V.1 ≤ Submodule.span K (Set.range A.row) := by
    intro v hv
    let a : K := v 0
    let z : Fin (m + 1) → K := v - a • top
    have hzV : z ∈ V.1 := by
      apply V.1.sub_mem hv
      exact V.1.smul_mem a htop_mem
    have hzhead : z 0 = 0 := by
      dsimp [z, a]
      rw [htop_zero]
      simp [smul_eq_mul]
    let zV : V.1 := ⟨z, hzV⟩
    let zker : f.ker := ⟨zV, ?_⟩
    · have htailW : echelonConsTail m z ∈ W := by
        refine ⟨zker, ?_⟩
        rfl
      rw [← hspanD] at htailW
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp htailW
      have htailEq (j : Fin m) :
          echelonConsTail m z j = ∑ i, c i * D.1 i j := by
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply,
          gk, g, zker, zV] using (congrFun hc j).symm
      have hzEq : echelonConsZero m (echelonConsTail m z) = z :=
        echelonConsZero_tail_of_head_eq_zero m z
          (by simpa [echelonConsHead_apply] using hzhead)
      have hsum : ∑ i, c i • A.row (Fin.succ i) ∈
          Submodule.span K (Set.range A.row) := by
        apply Submodule.sum_mem
        intro i hi
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.succ i, rfl⟩)
      have hsumEq : z = ∑ i, c i • A.row (Fin.succ i) := by
        rw [← hzEq]
        funext j
        cases j using Fin.cases with
        | zero =>
            rw [echelonConsZero_apply, Fin.cons_zero, Finset.sum_apply]
            simp only [Pi.smul_apply]
            change 0 = ∑ i, c i * lower i 0
            simp [lower, echelonConsZero]
        | succ j =>
            rw [echelonConsZero_apply, Fin.cons_succ, htailEq]
            rw [Finset.sum_apply]
            simp only [Pi.smul_apply]
            change ∑ i, c i * D.1 i j = ∑ i, c i * D.1 i j
            rfl
      have hzspan : z ∈ Submodule.span K (Set.range A.row) := by
        rw [hsumEq]
        exact hsum
      have hvEq : v = z + a • top := by
        dsimp [z]
        abel
      rw [hvEq]
      exact Submodule.add_mem _ hzspan
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    · apply LinearMap.mem_ker.mpr
      change z 0 = 0
      exact hzhead
  have hspan : Submodule.span K (Set.range A.row) = V.1 :=
    le_antisymm hAV hVA
  have hArank : A.rank = l'.succ := by
    rw [Matrix.rank_eq_finrank_span_row, hspan, V.2]
  let D' : EchelonMatrix K l'.succ (m + 1) :=
    ⟨A, hA, hArank⟩
  exact ⟨D', by
    apply Subtype.ext
    exact hspan⟩

/- The two branches above give the surjectivity part of the trijection by
   induction on the number of columns.  The zero-column case forces the row
   rank to be zero; in positive column dimension we split according to the
   first-coordinate projection. -/
theorem echelonRowSpace_surjective {l m : ℕ} :
    Function.Surjective
      (echelonRowSpace (K := K) (l := l) (m := m)) := by
  induction m generalizing l with
  | zero =>
      intro V
      have hV : V.1 = (⊥ : Submodule K (Fin 0 → K)) := by
        apply (Submodule.eq_bot_iff _).mpr
        intro v hv
        have hv0 : v = 0 := Subsingleton.elim _ _
        simpa [hv0]
      have hfin : Module.finrank K V.1 = 0 := by
        rw [hV]
        simp
      have hl : l = 0 := by omega
      subst l
      exact echelonRowSpace_surjective_zero V
  | succ m ih =>
      intro V
      by_cases hzero : ∀ v, v ∈ V.1 → v 0 = 0
      · exact echelonRowSpace_surjective_of_head_zero V hzero (ih (l := l))
      · push_neg at hzero
        obtain ⟨x, hx, hx0⟩ := hzero
        by_cases hl : l = 0
        · subst l
          exact echelonRowSpace_surjective_zero V
        · exact echelonRowSpace_surjective_of_head_ne_zero V x hx hx0
            (ih (l := l - 1)) (Nat.one_le_iff_ne_zero.mpr hl)

/- The trijection in Proposition `pr:trijection`, now discharged by the
   injectivity and constructive surjectivity proofs above. -/
def EchelonRowSpaceBridge (K : Type*) [Field K] [NumberField K]
    (l m : ℕ) : Prop :=
  Function.Bijective (echelonRowSpace (K := K) (l := l) (m := m))

theorem echelonRowSpace_injective {l m : ℕ} :
    Function.Injective (echelonRowSpace (K := K) (l := l) (m := m)) := by
  intro D E hDE
  apply Subtype.ext
  exact echelonMatrix_eq_of_rowSpace_eq hDE

theorem echelonRowSpaceBridge_iff_surjective {l m : ℕ} :
    EchelonRowSpaceBridge K l m ↔
      Function.Surjective (echelonRowSpace (K := K) (l := l) (m := m)) := by
  change Function.Bijective (echelonRowSpace (K := K) (l := l) (m := m)) ↔ _
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨echelonRowSpace_injective, h⟩

theorem echelonRowSpaceBridge {l m : ℕ} :
    EchelonRowSpaceBridge K l m := by
  exact echelonRowSpaceBridge_iff_surjective.mpr echelonRowSpace_surjective

/- `Equiv` form of Proposition `pr:trijection`; this is the reindexing form
   used whenever a paper sum over echelon matrices is written as a sum over
   rational row spaces. -/
noncomputable def echelonRowSpaceEquiv {l m : ℕ} :
    EchelonMatrix K l m ≃ Grassmannian K m l :=
  Equiv.ofBijective (echelonRowSpace (K := K) (l := l) (m := m))
    ⟨echelonRowSpace_injective, echelonRowSpace_surjective⟩

theorem tsum_echelon_reindex_rowSpaces {l m : ℕ}
    (F : EchelonMatrix K l m → ℝ) :
    (∑' D : EchelonMatrix K l m, F D) =
      ∑' V : Grassmannian K m l,
        F ((echelonRowSpaceEquiv (K := K) (l := l) (m := m)).symm V) := by
  exact (echelonRowSpaceEquiv (K := K) (l := l) (m := m)).symm.tsum_eq F |>.symm

theorem echelonRowSpace_rank {l m : ℕ} (D : EchelonMatrix K l m) :
    Module.finrank K (echelonRowSpace D).1 = l := by
  exact (echelonRowSpace D).2

theorem mem_calF_iff {l m n : ℕ} {Csup T : ℝ}
    {D : EchelonMatrix K l m} :
    D ∈ calF (K := K) (n := n) Csup T ↔
      ∃ A : echelonRowMatrixLattice D,
        rowMatrixRank (echelonRowSpace D) A = l ∧
        ‖((A.1 : rowMatrixRealSpan (echelonRowSpace D) n) :
            M n m (K_ℝ[K]))‖ ≤ Csup * T := by
  rfl

/- [paper, equation `eq:defi_of_calF`, lines 784--803] The same family written
with the manuscript's direct `M_n(Λ_D)` model. -/
noncomputable def calFDirect {l m n : ℕ}
    (Csup T : ℝ) : Set (EchelonMatrix K l m) :=
  {D | ∃ A : echelonIntegralMatrices (n := n) D,
    integralMatrixRank A.1 = l ∧
      ‖embedMatrix A.1‖ ≤ Csup * T}

theorem calFDirect_eq_calF {l m n : ℕ} {Csup T : ℝ} :
    calFDirect (K := K) (l := l) (m := m) (n := n) Csup T =
      calF (K := K) (l := l) (m := m) (n := n) Csup T := by
  ext D
  constructor
  · rintro ⟨A, hArank, hAnorm⟩
    let V : Grassmannian K m l := echelonRowSpace D
    have hArows : A.1 ∈ integralRowMatrixModule V n := by
      rw [← echelonIntegralRowMatrixModule_eq D]
      exact A.2
    let AB : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A} :=
      ⟨A.1, hArows⟩
    let e := integralRowMatricesEquivRowMatrixZLattice V n
    let B : rowMatrixZLattice V n := e AB
    have hBrank : rowMatrixRank V B = l := by
      simpa [rowMatrixRank, B, e, AB] using hArank
    refine ⟨B, hBrank, ?_⟩
    have hcoe := integralRowMatricesEquivRowMatrixZLattice_coe V n AB
    change ‖((B.1 : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))‖ ≤
      Csup * T
    rw [show B = e AB by rfl, hcoe]
    exact hAnorm
  · rintro ⟨B, hBrank, hBnorm⟩
    let V : Grassmannian K m l := echelonRowSpace D
    let e := integralRowMatricesEquivRowMatrixZLattice V n
    let AB := e.symm B
    have hABrows : AB.1 ∈ echelonIntegralRowMatrixModule D n := by
      rw [echelonIntegralRowMatrixModule_eq D]
      exact AB.2
    have hArank : integralMatrixRank AB.1 = l := by
      simpa [rowMatrixRank, AB, e] using hBrank
    have hcoe := integralRowMatricesEquivRowMatrixZLattice_coe V n AB
    have heq : e AB = B := e.apply_symm_apply B
    refine ⟨⟨AB.1, hABrows⟩, hArank, ?_⟩
    rw [← hcoe, heq]
    exact hBnorm

end

end Katznelson
