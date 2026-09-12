import Katznelson.Counting.GeometryOfNumbers
import Katznelson.Counting.RowLattice
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Successive minima

This file begins the formalization of Definition `de:defi_of_successive`.
The paper chooses the lexicographically least vector among norm minimizers.
Here the ambient total order is kept explicit: it is the formal counterpart
of the fixed coordinate lexicographic order in the manuscript.  The order is
used only to make the chosen minimizer unambiguous.
-/

namespace Katznelson

open MeasureTheory Set Metric Module
open scoped Classical NumberField

section Argmin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [LinearOrder E]

/- A lattice subset has only finitely many points in a bounded ball.  This is
   the precise finiteness input behind the paper's discrete-set `argmin`. -/
theorem exists_lattice_argmin
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (A : Set L) (hA : A.Nonempty) :
    ∃ v : L, v ∈ A ∧
      (∀ w : L, w ∈ A → ‖(v : E)‖ ≤ ‖(w : E)‖) ∧
      (∀ w : L, w ∈ A → ‖(w : E)‖ = ‖(v : E)‖ → v ≤ w) := by
  obtain ⟨a, ha⟩ := hA
  let S : Set L := {v | v ∈ A ∧ ‖(v : E)‖ ≤ ‖(a : E)‖}
  have hSfinite : S.Finite := by
    apply (lattice_ball_finite L).subset
    intro v hv
    exact hv.2
  have hSnonempty : S.Nonempty := ⟨a, ha, le_rfl⟩
  obtain ⟨v₀, hv₀S, hv₀min⟩ :=
    Set.exists_min_image S (fun v : L => ‖(v : E)‖) hSfinite hSnonempty
  let M : Set L := {v | v ∈ S ∧ ‖(v : E)‖ = ‖(v₀ : E)‖}
  have hMfinite : M.Finite := hSfinite.subset (by
    intro v hv
    exact hv.1)
  have hMnonempty : M.Nonempty := ⟨v₀, hv₀S, rfl⟩
  let sM : Finset L := hMfinite.toFinset
  have hsM : sM.Nonempty := by
    exact hMfinite.toFinset_nonempty.mpr hMnonempty
  let v : L := sM.min' hsM
  have hvM : v ∈ M := by
    apply hMfinite.mem_toFinset.mp
    exact Finset.min'_mem sM hsM
  have hvnorm : ‖(v : E)‖ = ‖(v₀ : E)‖ := hvM.2
  have hvA : v ∈ A := hvM.1.1
  have hvmin : ∀ w : L, w ∈ A → ‖(v : E)‖ ≤ ‖(w : E)‖ := by
    intro w hw
    by_cases hbound : ‖(w : E)‖ ≤ ‖(a : E)‖
    · have hwS : w ∈ S := ⟨hw, hbound⟩
      exact hvnorm ▸ hv₀min w hwS
    · have haw : ‖(a : E)‖ < ‖(w : E)‖ := lt_of_not_ge hbound
      exact (hvnorm ▸ (hv₀S.2.trans_lt haw)).le
  have hvlex : ∀ w : L, w ∈ A → ‖(w : E)‖ = ‖(v : E)‖ → v ≤ w := by
    intro w hw hnorm
    have hv₀le : ‖(v₀ : E)‖ ≤ ‖(a : E)‖ := hv₀S.2
    have hwS : w ∈ S := by
      refine ⟨hw, ?_⟩
      rw [hnorm, hvnorm]
      exact hv₀le
    have hwM : w ∈ M := ⟨hwS, by rw [hnorm, hvnorm]⟩
    exact Finset.min'_le sM w (hMfinite.mem_toFinset.mpr hwM)
  exact ⟨v, hvA, hvmin, hvlex⟩

noncomputable def latticeArgmin
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (A : Set L) (hA : A.Nonempty) : L :=
  Classical.choose (exists_lattice_argmin L A hA)

theorem latticeArgmin_mem
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (A : Set L) (hA : A.Nonempty) :
    latticeArgmin L A hA ∈ A :=
  (Classical.choose_spec (exists_lattice_argmin L A hA)).1

theorem latticeArgmin_norm_min
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (A : Set L) (hA : A.Nonempty) (w : L) (hw : w ∈ A) :
    ‖((latticeArgmin L A hA : L) : E)‖ ≤ ‖(w : E)‖ :=
  (Classical.choose_spec (exists_lattice_argmin L A hA)).2.1 w hw

theorem latticeArgmin_le_of_norm_eq
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (A : Set L) (hA : A.Nonempty) (w : L) (hw : w ∈ A)
    (hnorm : ‖(w : E)‖ = ‖((latticeArgmin L A hA : L) : E)‖) :
    latticeArgmin L A hA ≤ w :=
  (Classical.choose_spec (exists_lattice_argmin L A hA)).2.2 w hw hnorm

section FirstMinimum

variable [Nontrivial E]

/- The first minimum is the paper's `l₁`, provided the lattice has a nonzero
   vector.  Its norm-minimality is the part used immediately in the first
   clause of `le:props_of_minima`. -/
  noncomputable def firstMinimum
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : L ≠ ⊥) : L :=
  latticeArgmin L {v | v ≠ 0} (by
    obtain ⟨v, hvL, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
    exact ⟨⟨v, hvL⟩, by simpa using hv⟩)

theorem firstMinimum_ne_zero
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : L ≠ ⊥) : firstMinimum L hL ≠ 0 := by
  change latticeArgmin L {v : L | v ≠ 0} _ ∈ {v : L | v ≠ 0}
  exact latticeArgmin_mem L {v : L | v ≠ 0} _

theorem firstMinimum_norm_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : L ≠ ⊥) (w : L) (hw : w ≠ 0) :
    ‖((firstMinimum L hL : L) : E)‖ ≤ ‖(w : E)‖ := by
  apply latticeArgmin_norm_min
  exact hw

theorem firstMinimum_norm_le_covolume_rpow
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : L ≠ ⊥) :
    ‖((firstMinimum L hL : L) : E)‖ ≤
      minkowskiConstant (E := E) *
        (ZLattice.covolume L) ^ (1 / (Module.finrank ℝ E : ℝ)) := by
  obtain ⟨v, hv, hbound⟩ :=
    exists_nonzero_latticeVector_norm_le_covolume_rpow L
  exact (firstMinimum_norm_le L hL v hv).trans hbound

end FirstMinimum

end Argmin

section RecursiveMinima

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [LinearOrder E]

/- The `K`-span of the previously selected vectors, matching the `K · l_i`
   notation in Definition `de:defi_of_successive`.  The scalar type is kept
   generic so this recursion can also serve as a reusable algebraic interface. -/
noncomputable def previousKSpan
    (S : Type*) [Semiring S] [Module S E]
    (L : Submodule ℤ E) (i : ℕ) (v : Fin i → L) :
    Submodule S E :=
  Submodule.span S (Set.range (fun j => (v j : E)))

noncomputable def successiveMinimumSet
    (S : Type*) [Semiring S] [Module S E]
    (i : ℕ) (L : Submodule ℤ E) (v : Fin i → L) :
    Set L :=
  {w | (w : E) ∉ previousKSpan S L i v}

/- The recursive choice is total as a Lean definition.  Under the
   full-rank hypothesis used below, the fallback branch is impossible; it is
   included only so the definition itself does not hide an existence axiom. -/
noncomputable def successiveMinimaAux
    (S : Type*) [Semiring S] [Module S E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∀ i : ℕ, Fin i → L
  | 0 => Fin.elim0
  | i + 1 =>
      let prev := successiveMinimaAux S L i
      let A := successiveMinimumSet S i L prev
      Fin.snoc prev (if hA : A.Nonempty then latticeArgmin L A hA else 0)

noncomputable def successiveMinimum
    (S : Type*) [Semiring S] [Module S E] {k : ℕ}
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (i : Fin k) : L :=
  successiveMinimaAux S L (i.val + 1)
    ⟨i.val, Nat.lt_succ_self i.val⟩

theorem previousKSpan_zero
    {S : Type*} [Semiring S] [Module S E]
    (L : Submodule ℤ E) (v : Fin 0 → L) :
    previousKSpan S L 0 v = ⊥ := by
  simp [previousKSpan]

theorem successiveMinimumSet_zero
    {S : Type*} [Semiring S] [Module S E]
    (L : Submodule ℤ E) (v : Fin 0 → L) :
    successiveMinimumSet S 0 L v = {w : L | (w : E) ≠ 0} := by
  ext w
  simp [successiveMinimumSet, previousKSpan]

section ScalarMinima

variable {S : Type*} [Semiring S] [Module S E]

theorem successiveMinimaAux_castSucc
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : ℕ) (j : Fin i) :
    successiveMinimaAux S L (i + 1) j.castSucc =
      successiveMinimaAux S L i j := by
  simp [successiveMinimaAux]

/- [derived consequence of `de:defi_of_successive`, lines 871--879] The
   `K`-span of an initial segment of the recursive minima is contained in the
   span of every longer initial segment. -/
theorem previousKSpan_successiveMinimaAux_mono
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∀ {i j : ℕ} (hij : i ≤ j),
      previousKSpan S L i (successiveMinimaAux S L i) ≤
        previousKSpan S L j (successiveMinimaAux S L j) := by
  intro i j
  induction j with
  | zero =>
      intro hij
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      rfl
  | succ j ih =>
      intro hij
      by_cases hEq : i = j + 1
      · subst i
        exact le_rfl
      · have hij' : i ≤ j := by omega
        have hprev := ih hij'
        have hstep :
            previousKSpan S L j (successiveMinimaAux S L j) ≤
              previousKSpan S L (j + 1)
                (successiveMinimaAux S L (j + 1)) := by
          rw [previousKSpan, previousKSpan]
          apply Submodule.span_mono
          rintro x ⟨q, rfl⟩
          refine ⟨q.castSucc, ?_⟩
          simpa using congrArg (fun x : L => (x : E))
            (successiveMinimaAux_castSucc (S := S) L j q)
        exact hprev.trans hstep

/- The total recursive sequence agrees with the direct definition of the
   `i`-th minimum even when it is viewed inside a longer initial segment. -/
theorem successiveMinimum_eq_successiveMinimaAux
    {S : Type*} [Semiring S] [Module S E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∀ {k : ℕ} (i : Fin k),
      successiveMinimum S L i = successiveMinimaAux S L k i := by
  intro k
  induction k with
  | zero => intro i; exact Fin.elim0 i
  | succ k ih =>
      intro i
      by_cases hi : i.val < k
      · let j : Fin k := ⟨i.val, hi⟩
        have hcast : i = j.castSucc := by
          apply Fin.ext
          rfl
        rw [hcast, successiveMinimaAux_castSucc]
        exact ih j
      · have hilast : i = Fin.last k := by
          apply Fin.ext
          exact Nat.le_antisymm (Nat.le_of_lt_succ i.isLt) (not_lt.mp hi)
        rw [hilast]
        rfl

theorem successiveMinimaAux_last
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : ℕ) :
    successiveMinimaAux S L (i + 1) (Fin.last i) =
      if hA : (successiveMinimumSet S i L
        (successiveMinimaAux S L i)).Nonempty then
        latticeArgmin L (successiveMinimumSet S i L
          (successiveMinimaAux S L i)) hA
      else 0 := by
  simp [successiveMinimaAux]

theorem successiveMinimum_mem_of_nonempty
    {k : ℕ} (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : Fin k)
    (hA : (successiveMinimumSet S i.val L
      (successiveMinimaAux S L i.val)).Nonempty) :
    successiveMinimum S L i ∈ successiveMinimumSet S i.val L
      (successiveMinimaAux S L i.val) := by
  unfold successiveMinimum
  change successiveMinimaAux S L (i.val + 1) (Fin.last i.val) ∈ _
  rw [successiveMinimaAux_last]
  rw [dif_pos hA]
  exact latticeArgmin_mem L (successiveMinimumSet S i.val L
    (successiveMinimaAux S L i.val)) hA

theorem successiveMinimum_norm_min_of_nonempty
    {k : ℕ} (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : Fin k)
    (hA : (successiveMinimumSet S i.val L
      (successiveMinimaAux S L i.val)).Nonempty)
    (w : L) (hw : w ∈ successiveMinimumSet S i.val L
      (successiveMinimaAux S L i.val)) :
    ‖((successiveMinimum S L i : L) : E)‖ ≤ ‖(w : E)‖ := by
  have harg := latticeArgmin_norm_min L
    (successiveMinimumSet S i.val L
      (successiveMinimaAux S L i.val)) hA w hw
  unfold successiveMinimum
  change ‖((successiveMinimaAux S L (i.val + 1)
      (Fin.last i.val) : L) : E)‖ ≤ ‖(w : E)‖
  rw [successiveMinimaAux_last]
  simp [hA]
  exact harg

end ScalarMinima

section FieldRank

variable {K : Type*} [Field K] [Module K E]

/- Derived consequence for the special case where the scalar type is a field.
   This is the field-valued rank argument used by the manuscript's `K`-span
   definition; the later projection statement separately uses `K_ℝ`. -/
/- If the previously selected vectors are independent, their `K`-span cannot
   already contain the whole rank-`k` lattice span while fewer than `k`
   vectors have been selected.  Thus the next minimization set is nonempty. -/
theorem successiveMinimumSet_nonempty_of_finrank
    (k : ℕ) (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hfull : Module.finrank K (Submodule.span K (L : Set E)) = k)
    (i : ℕ) (hi : i < k)
    (hLI : LinearIndependent K
      (fun j : Fin i =>
        ((successiveMinimaAux K L i j : L) : E))) :
    (successiveMinimumSet K i L
      (successiveMinimaAux K L i)).Nonempty := by
  by_contra hA
  have hLW : ∀ w : L, (w : E) ∈
      previousKSpan K L i (successiveMinimaAux K L i) := by
    intro w
    by_contra hw
    apply hA
    refine ⟨w, ?_⟩
    change (w : E) ∉ previousKSpan K L i
      (successiveMinimaAux K L i)
    exact hw
  have hUW : Submodule.span K (L : Set E) ≤
      previousKSpan K L i (successiveMinimaAux K L i) := by
    apply Submodule.span_le.2
    intro x hx
    exact hLW ⟨x, hx⟩
  have hWU : previousKSpan K L i (successiveMinimaAux K L i) ≤
      Submodule.span K (L : Set E) := by
    change Submodule.span K (Set.range (fun j : Fin i =>
      ((successiveMinimaAux K L i j : L) : E))) ≤
      Submodule.span K (L : Set E)
    apply Submodule.span_le.2
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span (show
      ((successiveMinimaAux K L i j : L) : E) ∈ (L : Set E) from
        (successiveMinimaAux K L i j).property)
  have hUW_eq : Submodule.span K (L : Set E) =
      previousKSpan K L i (successiveMinimaAux K L i) := le_antisymm hUW hWU
  have hspan_rank : Module.finrank K
      (previousKSpan K L i (successiveMinimaAux K L i)) = i := by
    rw [previousKSpan, finrank_span_eq_card hLI]
    simp
  have hki : k = i := by
    calc
      k = Module.finrank K (Submodule.span K (L : Set E)) := hfull.symm
      _ = Module.finrank K
          (previousKSpan K L i (successiveMinimaAux K L i)) :=
        congrArg (fun S : Submodule K E => Module.finrank K S) hUW_eq
      _ = i := hspan_rank
  omega

/- The recursive construction consequently has independent initial segments
   through every index allowed by the lattice rank. -/
theorem successiveMinimaAux_linearIndependent_of_finrank
    (k : ℕ) (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hfull : Module.finrank K (Submodule.span K (L : Set E)) = k) :
    ∀ i : ℕ, i ≤ k →
      LinearIndependent K
        (fun j : Fin i =>
          ((successiveMinimaAux K L i j : L) : E)) := by
  intro i
  induction i with
  | zero =>
      intro _
      exact linearIndependent_empty_type
  | succ i ih =>
      intro hi
      have hip : i < k := lt_of_lt_of_le (Nat.lt_succ_self i) hi
      have hprev : LinearIndependent K
          (fun j : Fin i =>
            ((successiveMinimaAux K L i j : L) : E)) :=
        ih (Nat.le_of_lt hip)
      have hA := successiveMinimumSet_nonempty_of_finrank
        (K := K) k L hfull i hip hprev
      have hmem := latticeArgmin_mem L
        (successiveMinimumSet K i L (successiveMinimaAux K L i)) hA
      have hnew :
          ((latticeArgmin L (successiveMinimumSet K i L
            (successiveMinimaAux K L i)) hA : L) : E) ∉
            previousKSpan K L i (successiveMinimaAux K L i) := by
        change latticeArgmin L (successiveMinimumSet K i L
          (successiveMinimaAux K L i)) hA ∈
          successiveMinimumSet K i L (successiveMinimaAux K L i) at hmem
        exact hmem
      have hsnoc := hprev.finSnoc hnew
      have hfun :
          (fun j : Fin (i + 1) =>
            ((successiveMinimaAux K L (i + 1) j : L) : E)) =
          Fin.snoc
            (fun j : Fin i =>
              ((successiveMinimaAux K L i j : L) : E))
            ((latticeArgmin L (successiveMinimumSet K i L
              (successiveMinimaAux K L i)) hA : L) : E) := by
        funext j
        by_cases hj : j.val < i
        · simp [successiveMinimaAux, hA, Fin.snoc, hj]
        · simp [successiveMinimaAux, hA, Fin.snoc, hj]
      rw [hfun]
      exact hsnoc

/- [derived consequence of `de:defi_of_successive`, lines 871--879] Under
   the full-rank hypothesis, the admissible set at every indexed stage is
   nonempty.  This packages the rank argument above in the `Fin k` form used
   by the Euclidean supporting argument for Fieker--Stehlé Theorem 2. -/
theorem successiveMinimumSet_nonempty_of_finrank_at
    (k : ℕ) (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hfull : Module.finrank K (Submodule.span K (L : Set E)) = k)
    (i : Fin k) :
    (successiveMinimumSet K i.val L
      (successiveMinimaAux K L i.val)).Nonempty := by
  apply successiveMinimumSet_nonempty_of_finrank k L hfull i.val i.isLt
  exact successiveMinimaAux_linearIndependent_of_finrank k L hfull i.val
    (Nat.le_of_lt i.isLt)

/- [derived consequence of `de:defi_of_successive`, lines 871--879] The
   selected vector at an admissible full-rank stage lies outside the span of
   its predecessors. -/
theorem successiveMinimum_mem_of_finrank
    (k : ℕ) (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hfull : Module.finrank K (Submodule.span K (L : Set E)) = k)
    (i : Fin k) :
    successiveMinimum K L i ∈ successiveMinimumSet K i.val L
      (successiveMinimaAux K L i.val) :=
  successiveMinimum_mem_of_nonempty L i
    (successiveMinimumSet_nonempty_of_finrank_at k L hfull i)

/- [derived consequence of `de:defi_of_successive`, lines 871--879] Each
   selected minimum is nonzero because zero belongs to every predecessor
   span. -/
theorem successiveMinimum_ne_zero_of_finrank
    (k : ℕ) (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hfull : Module.finrank K (Submodule.span K (L : Set E)) = k)
    (i : Fin k) :
    successiveMinimum K L i ≠ 0 := by
  have hmem := successiveMinimum_mem_of_finrank k L hfull i
  intro hzero
  apply hmem
  rw [hzero]
  exact Submodule.zero_mem _

/- [derived consequence of `de:defi_of_successive`, lines 871--879] The
   indexed successive minima form a linearly independent family whenever the
   lattice span has the indicated field rank. -/
theorem successiveMinimum_linearIndependent_of_finrank
    (k : ℕ) (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hfull : Module.finrank K (Submodule.span K (L : Set E)) = k) :
    LinearIndependent K (fun i : Fin k =>
      ((successiveMinimum K L i : L) : E)) := by
  have haux := successiveMinimaAux_linearIndependent_of_finrank
    (K := K) k L hfull k le_rfl
  have hfun : (fun i : Fin k =>
      ((successiveMinimum K L i : L) : E)) =
      (fun i : Fin k =>
        ((successiveMinimaAux K L k i : L) : E)) := by
    funext i
    exact congrArg (fun x : L => (x : E))
      (successiveMinimum_eq_successiveMinimaAux (S := K) L i)
  rw [hfun]
  exact haux

/- [derived consequence of `de:defi_of_successive`, lines 871--879] The
   recursively selected norms are nondecreasing at every full-rank field
   lattice.  The row-space lemma below is its manuscript-facing specialization. -/
theorem successiveMinimum_norm_le_of_index_le_of_finrank
    (k : ℕ) (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hfull : Module.finrank K (Submodule.span K (L : Set E)) = k)
    (i j : Fin k) (hij : i.val ≤ j.val) :
    ‖((successiveMinimum K L i : L) : E)‖ ≤
      ‖((successiveMinimum K L j : L) : E)‖ := by
  by_cases hEq : i.val = j.val
  · have hij' : i = j := Fin.ext hEq
    subst hij'
    exact le_rfl
  · have hlt : i.val < j.val := lt_of_le_of_ne hij hEq
    have hmono := previousKSpan_successiveMinimaAux_mono
      (S := K) (L := L) (Nat.le_of_lt hlt)
    have hmemj := successiveMinimum_mem_of_finrank k L hfull j
    have hnotj :
        ((successiveMinimum K L j : L) : E) ∉
          previousKSpan K L j.val
            (successiveMinimaAux K L j.val) := hmemj
    have hnoti :
        ((successiveMinimum K L j : L) : E) ∉
          previousKSpan K L i.val
            (successiveMinimaAux K L i.val) := by
      intro hi
      exact hnotj (hmono hi)
    have hmemi : successiveMinimum K L j ∈
        successiveMinimumSet K i.val L
          (successiveMinimaAux K L i.val) := hnoti
    exact successiveMinimum_norm_min_of_nonempty L i
      (successiveMinimumSet_nonempty_of_finrank_at k L hfull i)
      (successiveMinimum K L j) hmemi

end FieldRank

end RecursiveMinima

section ModuleMinima

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [LinearOrder E]
  {K : Type*} [Field K] [Module K E]

/- The following is the radius formulation of the module minima used in
   Fieker--Stehlé, [FD10, Theorem 2].  It is an auxiliary interface for the
   cited product estimate, not a replacement for the manuscript's recursively
   defined l_i. -/
noncomputable def moduleMinimumAdmissibleRadii
    (L : Submodule ℤ E) {k : ℕ} (i : Fin k) : Set ℝ :=
  {r | ∃ v : Fin (i.val + 1) → L,
    LinearIndependent K (fun j => ((v j : L) : E)) ∧
      ∀ j, ‖((v j : L) : E)‖ ≤ r}

noncomputable def moduleMinimum
    (L : Submodule ℤ E) {k : ℕ} (i : Fin k) : ℝ :=
  sInf (moduleMinimumAdmissibleRadii (K := K) L i)

theorem moduleMinimum_nonneg_of_nonempty
    (L : Submodule ℤ E) {k : ℕ} (i : Fin k)
    (hA : (moduleMinimumAdmissibleRadii (K := K) L i).Nonempty) :
    0 ≤ moduleMinimum (K := K) L i := by
  apply le_csInf hA
  intro r hr
  obtain ⟨v, _, hvr⟩ := hr
  exact le_trans (norm_nonneg _) (hvr (0 : Fin (i.val + 1)))

theorem moduleMinimum_le_sup_norm_of_linearIndependent
    (L : Submodule ℤ E) {k : ℕ} (i : Fin k)
    (v : Fin (i.val + 1) → L)
    (hv : LinearIndependent K (fun j => ((v j : L) : E))) :
    moduleMinimum (K := K) L i ≤
      (Finset.univ.sup' (Finset.univ_nonempty :
        (Finset.univ : Finset (Fin (i.val + 1))).Nonempty)
        (fun j => ‖((v j : L) : E)‖)) := by
  let A := moduleMinimumAdmissibleRadii (K := K) L i
  have hbelow : BddBelow A := by
    refine ⟨0, ?_⟩
    rintro r ⟨w, _, hw⟩
    exact le_trans (norm_nonneg _) (hw (0 : Fin (i.val + 1)))
  have hsup : ∀ j : Fin (i.val + 1),
      ‖((v j : L) : E)‖ ≤
        Finset.univ.sup' (Finset.univ_nonempty :
          (Finset.univ : Finset (Fin (i.val + 1))).Nonempty)
          (fun j => ‖((v j : L) : E)‖) := by
    intro j
    exact Finset.le_sup'
      (s := (Finset.univ : Finset (Fin (i.val + 1))))
      (f := fun j => ‖((v j : L) : E)‖) (Finset.mem_univ j)
  have hmem : (Finset.univ.sup' (Finset.univ_nonempty :
      (Finset.univ : Finset (Fin (i.val + 1))).Nonempty)
      (fun j => ‖((v j : L) : E)‖)) ∈ A := ⟨v, hv, hsup⟩
  exact csInf_le hbelow hmem

/- If the preceding recursive vectors are independent, the next manuscript
   minimum is no larger than every admissible module radius.  The proof uses
   only the finite-ball argmin and the K-span exclusion in the manuscript's
   definition. -/
theorem successiveMinimum_norm_le_moduleMinimum
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {k : ℕ} (i : Fin k)
    (hA : (successiveMinimumSet K i.val L
      (successiveMinimaAux K L i.val)).Nonempty)
    (hprev : LinearIndependent K (fun j : Fin i.val =>
      ((successiveMinimaAux K L i.val j : L) : E))) :
    ‖((successiveMinimum K L i : L) : E)‖ ≤
      moduleMinimum (K := K) L i := by
  let A := moduleMinimumAdmissibleRadii (K := K) L i
  have hbound : ∀ r ∈ A, ‖((successiveMinimum K L i : L) : E)‖ ≤ r := by
    intro r hr
    obtain ⟨v, hv, hvr⟩ := hr
    have hex : ∃ j : Fin (i.val + 1),
        (v j : E) ∉ previousKSpan K L i.val
          (successiveMinimaAux K L i.val) := by
      by_contra hno
      have hall : ∀ j : Fin (i.val + 1),
          (v j : E) ∈ previousKSpan K L i.val
            (successiveMinimaAux K L i.val) := by
        intro j
        by_contra hj
        exact hno ⟨j, hj⟩
      have hspan : Submodule.span K (Set.range (fun j : Fin (i.val + 1) =>
          (v j : E))) ≤ previousKSpan K L i.val
            (successiveMinimaAux K L i.val) := by
        apply Submodule.span_le.2
        intro x hx
        obtain ⟨j, rfl⟩ := hx
        exact hall j
      have hdim : i.val + 1 ≤ i.val := by
        letI : FiniteDimensional K
            (previousKSpan K L i.val (successiveMinimaAux K L i.val)) :=
          FiniteDimensional.span_of_finite K (Set.finite_range _)
        have h := Submodule.finrank_mono hspan
        rw [finrank_span_eq_card hv, previousKSpan,
          finrank_span_eq_card hprev] at h
        simpa using h
      omega
    obtain ⟨j, hj⟩ := hex
    have hnorm := successiveMinimum_norm_min_of_nonempty
      (S := K) L i hA (v j) hj
    exact hnorm.trans (hvr j)
  have hAnonempty : A.Nonempty := by
    have hmem := successiveMinimum_mem_of_nonempty
      (S := K) L i hA
    have hnew : ((successiveMinimum K L i : L) : E) ∉
        previousKSpan K L i.val (successiveMinimaAux K L i.val) := hmem
    let w : Fin (i.val + 1) → L :=
      Fin.snoc (successiveMinimaAux K L i.val)
        (successiveMinimum K L i)
    have hw : LinearIndependent K (fun j : Fin (i.val + 1) =>
        ((w j : L) : E)) := by
      have hfun : (fun j : Fin (i.val + 1) =>
          ((w j : L) : E)) =
        Fin.snoc (fun j : Fin i.val =>
          ((successiveMinimaAux K L i.val j : L) : E))
          ((successiveMinimum K L i : L) : E) := by
        funext j
        by_cases hj : j.val < i.val
        · simp [w, Fin.snoc, hj]
        · simp [w, Fin.snoc, hj]
      rw [hfun]
      exact hprev.finSnoc hnew
    refine ⟨Finset.univ.sup' (Finset.univ_nonempty :
        (Finset.univ : Finset (Fin (i.val + 1))).Nonempty)
        (fun j => ‖((w j : L) : E)‖), ⟨w, hw, ?_⟩⟩
    intro j
    exact Finset.le_sup'
      (s := (Finset.univ : Finset (Fin (i.val + 1))))
      (f := fun j => ‖((w j : L) : E)‖) (Finset.mem_univ j)
  exact le_csInf hAnonempty hbound

end ModuleMinima

section RowSuccessiveMinima

variable {K : Type*} [Field K] [NumberField K]
  {m k : ℕ} (V : Grassmannian K m k)

/- The following are the same induced Euclidean structures used in
   `RowLattice`.  They are restated locally because those declarations are
   intentionally local there; this keeps the public specialization below
   independent of hidden typeclass state. -/
noncomputable local instance rowSuccessiveAmbientMeasurableSpace :
    MeasurableSpace (RowVector K m) := borel (RowVector K m)

local instance rowSuccessiveAmbientBorelSpace :
    @BorelSpace (RowVector K m) _ rowSuccessiveAmbientMeasurableSpace :=
  ⟨rfl⟩

noncomputable local instance rowSuccessiveMeasurableSpace :
    MeasurableSpace (rowRealSpan V) :=
  @Subtype.instMeasurableSpace (RowVector K m)
    (fun x => x ∈ rowRealSpan V) rowSuccessiveAmbientMeasurableSpace

local instance rowSuccessiveBorelSpace :
    BorelSpace (rowRealSpan V) :=
  @Subtype.borelSpace (RowVector K m) _ rowSuccessiveAmbientMeasurableSpace
    rowSuccessiveAmbientBorelSpace (fun x => x ∈ rowRealSpan V)

noncomputable local instance rowSuccessiveNormedSpace :
    NormedSpace ℝ (rowRealSpan V) :=
  Submodule.normedSpace (rowRealSpan V)

noncomputable local instance rowSuccessiveInnerProductSpace :
    InnerProductSpace ℝ (rowRealSpan V) :=
  Submodule.innerProductSpace (rowRealSpan V)

/- Definition `de:defi_of_successive`, with the manuscript's number-field
   scalar `K` made explicit.  The recursive definition has a fallback only
   for totality; the nonempty-set obligations are discharged below from the
   real dimension of the embedded `𝓞_K`-lattice. -/
noncomputable def rowSuccessiveMinimum (i : Fin k) : rowZLattice V :=
  successiveMinimum K (rowZLattice V) i

theorem rowSuccessiveMinimum_mem_of_nonempty
    (i : Fin k)
    (hA : (successiveMinimumSet K i.val (rowZLattice V)
      (successiveMinimaAux K (rowZLattice V) i.val)).Nonempty) :
    rowSuccessiveMinimum V i ∈ successiveMinimumSet K i.val
      (rowZLattice V) (successiveMinimaAux K (rowZLattice V) i.val) := by
  exact successiveMinimum_mem_of_nonempty
    (S := K) (L := rowZLattice V) i hA

theorem rowSuccessiveMinimum_norm_min_of_nonempty
    (i : Fin k)
    (hA : (successiveMinimumSet K i.val (rowZLattice V)
      (successiveMinimaAux K (rowZLattice V) i.val)).Nonempty)
    (w : rowZLattice V)
    (hw : w ∈ successiveMinimumSet K i.val (rowZLattice V)
      (successiveMinimaAux K (rowZLattice V) i.val)) :
      ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ≤
      ‖(w : rowRealSpan V)‖ := by
  exact successiveMinimum_norm_min_of_nonempty
    (S := K) (L := rowZLattice V) i hA w hw

/- The selected minima are `K`-linearly independent.  The rank bridge for
   the `K`-span of the row lattice is proved in `RowLattice`; this theorem is
   the recursive-independence consequence used when the paper passes from
   `K l_1 + ... + K l_k` to the full rational row space. -/
theorem rowSuccessiveMinimum_linearIndependent :
    LinearIndependent K (fun i : Fin k =>
      ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)) := by
  have hfull : Module.finrank K
      (Submodule.span K (rowZLattice V : Set (rowRealSpan V))) = k :=
    rowZLattice_K_span_finrank V
  have hLI := successiveMinimaAux_linearIndependent_of_finrank
    (E := rowRealSpan V) (K := K) k (rowZLattice V) hfull
      (i := k) le_rfl
  have hbridge : ∀ i : Fin k,
      successiveMinimum K (rowZLattice V) i =
        successiveMinimaAux K (rowZLattice V) k i :=
    successiveMinimum_eq_successiveMinimaAux (S := K) (rowZLattice V)
  rw [show (fun i : Fin k =>
      ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)) =
      (fun i : Fin k =>
        ((successiveMinimaAux K (rowZLattice V) k i : rowZLattice V) :
          rowRealSpan V)) by
    funext i
    exact congrArg (fun x : rowZLattice V => (x : rowRealSpan V))
      (hbridge i)]
  exact hLI

/- The selected vectors generate the rational `K`-span of the lattice. -/
theorem rowSuccessiveMinimum_K_span_eq_rowZLattice_K_span :
    Submodule.span K (Set.range (fun i : Fin k =>
      ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V))) =
      Submodule.span K (rowZLattice V : Set (rowRealSpan V)) := by
  have hLI := rowSuccessiveMinimum_linearIndependent V
  have hle : Submodule.span K (Set.range (fun i : Fin k =>
      ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V))) ≤
      Submodule.span K (rowZLattice V : Set (rowRealSpan V)) := by
    apply Submodule.span_mono
    rintro x ⟨i, rfl⟩
    exact (rowSuccessiveMinimum V i).property
  have hsel : Module.finrank K (Submodule.span K (Set.range (fun i : Fin k =>
      ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)))) = k := by
    rw [finrank_span_eq_card hLI]
    simp
  letI : FiniteDimensional K
      (Submodule.span K (rowZLattice V : Set (rowRealSpan V))) :=
    rowZLattice_K_span_finiteDimensional V
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [hsel, rowZLattice_K_span_finrank V]

/- [derived consequence, paper `le:injective_minima`, lines 1211--1233,
   together with Proposition `pr:trijection`, lines 780--795] The selected
   minima determine the embedded rational row space.  The left side retains
   the manuscript's tuple of integral rows; the right side is the proved
   row-space embedding bridge used to recover the Grassmannian point. -/
theorem rowSuccessiveMinimum_ambient_span_eq_range
    : Submodule.span K (Set.range (fun i : Fin k =>
        (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
          RowVector K m))) =
      LinearMap.range (rowSpaceVectorEmbeddingK V) := by
  let f : rowRealSpan V →ₗ[K] RowVector K m :=
    rowRealSpanSubtypeKLinearMap V
  let S : Submodule K (rowRealSpan V) :=
    Submodule.span K (Set.range (fun i : Fin k =>
      ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)))
  have hmap_min : S.map f =
      Submodule.span K (Set.range (fun i : Fin k =>
        (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
          RowVector K m))) := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V),
        ⟨i, rfl⟩, rfl⟩
  have hmap_lattice :
      (Submodule.span K (rowZLattice V : Set (rowRealSpan V))).map f =
        Submodule.span K (embeddedIntegralRowModule V : Set (RowVector K m)) := by
    rw [Submodule.map_span]
    rw [rowRealSpanSubtypeKLinearMap_image_rowZLattice V]
  calc
    Submodule.span K (Set.range (fun i : Fin k =>
        (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
          RowVector K m))) = S.map f := hmap_min.symm
    _ = (Submodule.span K (rowZLattice V : Set (rowRealSpan V))).map f := by
      dsimp [S]
      rw [rowSuccessiveMinimum_K_span_eq_rowZLattice_K_span V]
    _ = Submodule.span K (embeddedIntegralRowModule V : Set (RowVector K m)) :=
      hmap_lattice
    _ = LinearMap.range (rowSpaceVectorEmbeddingK V) :=
      span_embeddedIntegralRowModule_eq_range_rowSpaceVectorEmbeddingK V

/- [paper `le:injective_minima`, lines 1211--1233] Equality of two selected
   minima tuples forces equality of their rational row spaces, hence equality
   of the corresponding points of the Grassmannian.  This is the explicit
   bridge from the manuscript's tuple to the trijection representation. -/
theorem rowSuccessiveMinimum_ambient_tuple_injective
    {m k : ℕ} :
    Function.Injective (fun V : Grassmannian K m k =>
      fun i : Fin k =>
        (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
          RowVector K m)) := by
  intro V W hVW
  have hspan :
      LinearMap.range (rowSpaceVectorEmbeddingK V) =
        LinearMap.range (rowSpaceVectorEmbeddingK W) := by
    calc
      LinearMap.range (rowSpaceVectorEmbeddingK V) =
          Submodule.span K (Set.range (fun i : Fin k =>
            (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
              RowVector K m))) :=
        (rowSuccessiveMinimum_ambient_span_eq_range V).symm
      _ = Submodule.span K (Set.range (fun i : Fin k =>
            (((rowSuccessiveMinimum W i : rowZLattice W) : rowRealSpan W) :
              RowVector K m))) := by
        rw [show (fun i : Fin k =>
            (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
              RowVector K m)) =
            (fun i : Fin k =>
            (((rowSuccessiveMinimum W i : rowZLattice W) : rowRealSpan W) :
              RowVector K m)) by exact hVW]
      _ = LinearMap.range (rowSpaceVectorEmbeddingK W) :=
        rowSuccessiveMinimum_ambient_span_eq_range W
  have hsub : V.1 ≤ W.1 := by
    intro x hx
    obtain ⟨y, hy⟩ := hspan ▸
      (show rowSpaceVectorEmbeddingK V ⟨x, hx⟩ ∈
        LinearMap.range (rowSpaceVectorEmbeddingK V) from ⟨⟨x, hx⟩, rfl⟩)
    have hxy : (y : Fin m → K) = x := by
      funext j
      apply numberEmbedding_injective K
      exact congrArg (fun z : RowVector K m => z j) hy
    exact hxy ▸ y.property
  have hsub' : W.1 ≤ V.1 := by
    intro x hx
    obtain ⟨y, hy⟩ := hspan.symm ▸
      (show rowSpaceVectorEmbeddingK W ⟨x, hx⟩ ∈
        LinearMap.range (rowSpaceVectorEmbeddingK W) from ⟨⟨x, hx⟩, rfl⟩)
    have hxy : (y : Fin m → K) = x := by
      funext j
      apply numberEmbedding_injective K
      exact congrArg (fun z : RowVector K m => z j) hy
    exact hxy ▸ y.property
  apply Subtype.ext
  exact le_antisymm hsub hsub'

/- The `K_ℝ`-span of the selected minima is the full real row span.  This is
   the span identity used in the proof of part 2 of `le:props_of_minima`; the
   fundamental domain for `𝓞_K` is handled separately. -/
theorem rowSuccessiveMinimum_KRealSpan_eq_top :
    Submodule.span K_ℝ[K] (Set.range (fun i : Fin k =>
      ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V))) = ⊤ := by
  let S : Submodule K (rowRealSpan V) :=
    Submodule.span K (Set.range (fun i : Fin k =>
      ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)))
  let SR : Submodule K_ℝ[K] (rowRealSpan V) :=
    Submodule.span K_ℝ[K] (Set.range (fun i : Fin k =>
      ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)))
  have hKS : S = Submodule.span K (rowZLattice V : Set (rowRealSpan V)) := by
    exact rowSuccessiveMinimum_K_span_eq_rowZLattice_K_span V
  have hSK : S ≤ SR.restrictScalars K := by
    exact Submodule.span_le_restrictScalars K K_ℝ[K] _
  have hrow : Submodule.span K (rowZLattice V : Set (rowRealSpan V)) ≤
      SR.restrictScalars K := hKS ▸ hSK
  have hreal : Submodule.span ℝ (rowZLattice V : Set (rowRealSpan V)) = ⊤ :=
    IsZLattice.span_top (K := ℝ) (L := rowZLattice V)
  have hreal_le : Submodule.span ℝ (rowZLattice V : Set (rowRealSpan V)) ≤
      SR.restrictScalars ℝ := by
    apply Submodule.span_le.2
    intro x hx
    exact hrow (Submodule.subset_span (R := K) hx)
  apply top_unique
  intro x hx
  have hxreal : x ∈ Submodule.span ℝ (rowZLattice V : Set (rowRealSpan V)) := by
    rw [hreal]
    exact hx
  exact hreal_le hxreal

/- The `K`-span of `v₁, ..., vᵢ` is contained in the range of the real-linear
   combination map from `(K_ℝ)ⁱ`.  The larger real coefficient space supplies
   the dimension bound while the recursive admissibility condition remains
   the manuscript's `K`-span condition. -/
noncomputable def rowKRealCombinationMap {i : ℕ}
    (v : Fin i → rowZLattice V) :
    (Fin i → K_ℝ[K]) →ₗ[ℝ] rowRealSpan V where
  toFun a := ∑ j, a j • (v j : rowRealSpan V)
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by
    simp only [Pi.smul_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact smul_assoc r (a j) (v j : rowRealSpan V)

@[simp]
theorem rowKRealCombinationMap_apply_single {i : ℕ}
    (v : Fin i → rowZLattice V) (j : Fin i) :
    rowKRealCombinationMap V v (Pi.single j 1) = v j := by
  simp [rowKRealCombinationMap]

theorem rowKRealCombinationMap_smul {i : ℕ}
    (v : Fin i → rowZLattice V) (c : K_ℝ[K])
    (a : Fin i → K_ℝ[K]) :
    c • rowKRealCombinationMap V v a =
      rowKRealCombinationMap V v (fun j => c * a j) := by
  change c • (∑ j, a j • (v j : rowRealSpan V)) =
    ∑ j, (c * a j) • (v j : rowRealSpan V)
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (mul_smul c (a j) (v j : rowRealSpan V)).symm

theorem mem_range_rowKRealCombinationMap_of_mem_previous {i : ℕ}
    (v : Fin i → rowZLattice V) {x : rowRealSpan V}
    (hx : x ∈ previousKSpan K (rowZLattice V) i v) :
    x ∈ LinearMap.range (rowKRealCombinationMap V v) := by
  rw [previousKSpan] at hx
  apply Submodule.span_induction
    (p := fun y _ => y ∈ LinearMap.range (rowKRealCombinationMap V v))
    ?_ ?_ ?_ ?_ hx
  · rintro y ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    simp
  · exact (LinearMap.range (rowKRealCombinationMap V v)).zero_mem
  · intro y z _ _ hy hz
    exact (LinearMap.range (rowKRealCombinationMap V v)).add_mem hy hz
  · intro c y _ hy
    rcases hy with ⟨a, rfl⟩
    refine ⟨fun j => numberEmbedding K c * a j, ?_⟩
    exact (rowKRealCombinationMap_smul V v (numberEmbedding K c) a).symm

theorem rowKRealCombinationMap_range_eq_top_of_previous_mem {i : ℕ}
    (v : Fin i → rowZLattice V)
    (hprev : ∀ w : rowZLattice V,
      (w : rowRealSpan V) ∈
        previousKSpan K (rowZLattice V) i v) :
    LinearMap.range (rowKRealCombinationMap V v) = ⊤ := by
  have hspan : Submodule.span ℝ (rowZLattice V : Set (rowRealSpan V)) = ⊤ :=
    IsZLattice.span_top (K := ℝ) (L := rowZLattice V)
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.2
  intro x hx
  have hx' : ((⟨x, hx⟩ : rowZLattice V) : rowRealSpan V) ∈
      previousKSpan K (rowZLattice V) i v := hprev ⟨x, hx⟩
  simpa using mem_range_rowKRealCombinationMap_of_mem_previous V v hx'

/- The same combination map is onto as soon as its selected vectors span the
   real scalar extension.  This is the linear-algebra form of the first line
   in the manuscript's parallelepiped argument. -/
theorem rowKRealCombinationMap_range_eq_top_of_KRealSpan {i : ℕ}
    (v : Fin i → rowZLattice V)
    (hspan : Submodule.span K_ℝ[K] (Set.range (fun j : Fin i =>
      ((v j : rowZLattice V) : rowRealSpan V))) = ⊤) :
    LinearMap.range (rowKRealCombinationMap V v) = ⊤ := by
  classical
  apply top_unique
  intro x hx
  have hxspan : x ∈ Submodule.span K_ℝ[K] (Set.range (fun j : Fin i =>
      ((v j : rowZLattice V) : rowRealSpan V))) := by
    rw [hspan]
    exact hx
  apply Submodule.span_induction
    (p := fun y _ => y ∈ LinearMap.range (rowKRealCombinationMap V v))
    ?_ ?_ ?_ ?_ hxspan
  · rintro y ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    simp [rowKRealCombinationMap]
  · exact (LinearMap.range (rowKRealCombinationMap V v)).zero_mem
  · intro y z _ _ hy hz
    exact (LinearMap.range (rowKRealCombinationMap V v)).add_mem hy hz
  · intro c y _ hy
    rcases hy with ⟨a, rfl⟩
    refine ⟨fun j => c * a j, ?_⟩
    exact (rowKRealCombinationMap_smul V v c a).symm

/- The fixed integral basis of `𝓞_K`, transported through the Euclidean
   realization of `K_ℝ`, is a real basis of the coefficient space. -/
noncomputable def numberFieldEuclideanBasis :
    Basis (IntegralBasisIndex K) ℝ K_ℝ[K] :=
  (NumberField.mixedEmbedding.latticeBasis K).map
    (NumberField.mixedEmbedding.euclidean.toMixed K).symm.toLinearEquiv

/- The real basis obtained by applying the coefficient basis to the selected
   minima.  Its vectors generate exactly the lattice
   `𝓞_K l₁ + ⋯ + 𝓞_K l_k`. -/
noncomputable def rowMinimaRealBasis :
    Basis (Σ _ : Fin k, IntegralBasisIndex K) ℝ (rowRealSpan V) := by
  letI : Fintype (IntegralBasisIndex K) := Fintype.ofFinite _
  let f := rowKRealCombinationMap V
    (fun i : Fin k => rowSuccessiveMinimum V i)
  have hspan : Submodule.span K_ℝ[K] (Set.range (fun i : Fin k =>
      ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V))) = ⊤ :=
    rowSuccessiveMinimum_KRealSpan_eq_top V
  have hrange : LinearMap.range f = ⊤ :=
    rowKRealCombinationMap_range_eq_top_of_KRealSpan V
      (fun i : Fin k => rowSuccessiveMinimum V i) hspan
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    exact hrange
  have hdim : Module.finrank ℝ (Fin k → K_ℝ[K]) =
      Module.finrank ℝ (rowRealSpan V) := by
    rw [rowRealSpan_finrank V, Module.finrank_pi_fintype]
    simp [NumberField.mixedEmbedding.euclidean.finrank, degree]
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  exact (Pi.basis (fun _ : Fin k => numberFieldEuclideanBasis (K := K))).map
    (f.linearEquivOfInjective hinj hdim)

theorem rowMinimaRealBasis_apply (i : Fin k) (j : IntegralBasisIndex K) :
    rowMinimaRealBasis V ⟨i, j⟩ =
      numberEmbedding K (NumberField.integralBasis K j) •
        (rowSuccessiveMinimum V i : rowRealSpan V) := by
  classical
  simp [rowMinimaRealBasis, numberFieldEuclideanBasis,
    rowKRealCombinationMap, numberEmbedding,
    NumberField.mixedEmbedding.latticeBasis_apply]

theorem numberFieldEuclideanBasis_apply (j : IntegralBasisIndex K) :
    numberFieldEuclideanBasis (K := K) j =
      numberEmbedding K (NumberField.integralBasis K j) := by
  simp [numberFieldEuclideanBasis, numberEmbedding,
    NumberField.mixedEmbedding.latticeBasis_apply]

theorem rowMinimaRealBasis_mem_rowZLattice
    (i : Fin k) (j : IntegralBasisIndex K) :
    rowMinimaRealBasis V ⟨i, j⟩ ∈ rowZLattice V := by
  classical
  rw [rowMinimaRealBasis_apply]
  rw [NumberField.integralBasis_apply]
  change numberEmbedding K
      (algebraMap (𝓞 K) K (NumberField.RingOfIntegers.basis K j)) •
      ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) ∈
      rowZLattice V
  change numberEmbedding K
      (algebraMap (𝓞 K) K (NumberField.RingOfIntegers.basis K j)) •
      ((rowSuccessiveMinimum V i : rowRealSpan V) : RowVector K m) ∈
      embeddedIntegralRowModule V
  exact embeddedIntegralRowModule_smul_integral V
    (NumberField.RingOfIntegers.basis K j)
    (rowSuccessiveMinimum V i).property

/- [derived consequence of part 2 of `le:props_of_minima`, lines 960--964]
   Scalar multiplication in the Euclidean realization is bilinear over ℝ.
   Finite-dimensional continuity therefore supplies the uniform constant in
   the manuscript's assertion that `v ∈ F₀ x` implies
   `‖v‖ ≤ C ‖x‖`. -/
theorem exists_rowKReal_smul_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ c : K_ℝ[K], ∀ x : RowVector K m,
      ‖c • x‖ ≤ C * ‖c‖ * ‖x‖ := by
  letI : IsModuleTopology ℝ K_ℝ[K] := isModuleTopologyOfFiniteDimensional
  letI : IsModuleTopology ℝ (RowVector K m) := isModuleTopologyOfFiniteDimensional
  let B : K_ℝ[K] →ₗ[ℝ] RowVector K m →ₗ[ℝ] RowVector K m :=
    LinearMap.mk₂ ℝ (fun c x => c • x)
      (by intro c c' x; exact add_smul c c' x)
      (by intro r c x; exact smul_assoc r c x)
      (by intro c x x'; exact smul_add c x x')
      (by intro r c x; exact smul_comm c r x)
  have hcont : Continuous (fun p : K_ℝ[K] × RowVector K m => B p.1 p.2) := by
    exact IsModuleTopology.continuous_bilinear_of_finite_left B
  let f : MultilinearMap ℝ (fun _ : Fin 2 => K_ℝ[K] × RowVector K m)
      (RowVector K m) :=
    MultilinearMap.mk' (fun a => B (a 0).1 (a 1).2)
      (by
        intro a i x y
        cases i using Fin.cases
        · simp [B, Function.update]
        · case succ i =>
          have hi : i = 0 := Fin.eq_zero i
          subst hi
          simp [B, Function.update])
      (by
        intro a i r x
        cases i using Fin.cases
        · simp [B, Function.update]
        · case succ i =>
          have hi : i = 0 := Fin.eq_zero i
          subst hi
          simp [B, Function.update])
  have hfcont : Continuous f := by
    have hcoords : Continuous
        (fun a : (∀ _ : Fin 2, K_ℝ[K] × RowVector K m) =>
          ((a 0).1, (a 1).2)) := by
      fun_prop
    exact hcont.comp hcoords
  obtain ⟨C, hC, hf⟩ := f.exists_bound_of_continuous hfcont
  refine ⟨C, hC, ?_⟩
  intro c x
  simpa [f, B, mul_assoc] using hf (Fin.cons (c, 0) (fun _ => (0, x)))

noncomputable def rowKRealSmulBound : ℝ :=
  Classical.choose (exists_rowKReal_smul_bound (K := K) (m := m))

theorem rowKRealSmulBound_pos : 0 < rowKRealSmulBound (K := K) (m := m) :=
  (Classical.choose_spec (exists_rowKReal_smul_bound (K := K) (m := m))).1

theorem rowKRealSmulBound_apply (c : K_ℝ[K]) (x : RowVector K m) :
    ‖c • x‖ ≤ rowKRealSmulBound (K := K) (m := m) * ‖c‖ * ‖x‖ :=
  (Classical.choose_spec (exists_rowKReal_smul_bound (K := K) (m := m))).2 c x

/- [derived consequence of part 2 of `le:props_of_minima`, lines 952--964]
   This is the radius of a fixed fundamental-domain substitute for the
   coefficient lattice `𝓞_K` in `K_ℝ`. -/
noncomputable def numberFieldCoefficientRadius
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  latticeCoveringRadius (NumberField.mixedEmbedding.euclidean.integerLattice K)

theorem exists_numberField_coefficient_approx (c : K_ℝ[K]) :
    ∃ a : 𝓞 K, ‖c - numberEmbedding K (a : K)‖ ≤ numberFieldCoefficientRadius K := by
  obtain ⟨v, hv⟩ := latticeCovering_latticeCoveringRadius
    (NumberField.mixedEmbedding.euclidean.integerLattice K) c
  have hv' : ‖c - (v : K_ℝ[K])‖ ≤ numberFieldCoefficientRadius K := by
    simpa [dist_eq_norm, numberFieldCoefficientRadius] using hv
  have hvlat : (v : K_ℝ[K]) ∈
      NumberField.mixedEmbedding.euclidean.integerLattice K := v.property
  change (NumberField.mixedEmbedding.euclidean.toMixed K) (v : K_ℝ[K]) ∈
      NumberField.mixedEmbedding.integerLattice K at hvlat
  rcases hvlat with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hva : (v : K_ℝ[K]) = numberEmbedding K (a : K) := by
    apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
    simpa [numberEmbedding] using ha.symm
  rw [hva] at hv'
  exact hv'

/- [derived consequence of the finite-dimensional realization of `K_ℝ`] For
   each fixed coefficient, scalar multiplication on the ambient row space is
   a real-linear map and therefore has a finite operator bound.  Working in
   the ambient space makes the resulting constant independent of the row
   subspace, as required by part 2 of `le:props_of_minima`. -/
noncomputable def rowKRealScalarLinearMap (c : K_ℝ[K]) :
    RowVector K m →ₗ[ℝ] RowVector K m where
  toFun x := c • x
  map_add' x y := by
    exact smul_add c x y
  map_smul' r x := by
    exact smul_comm c r x

theorem exists_rowKRealScalar_bound (c : K_ℝ[K]) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : RowVector K m,
      ‖c • x‖ ≤ C * ‖x‖ := by
  exact SemilinearMapClass.bound_of_continuous
    (rowKRealScalarLinearMap (m := m) c)
    (LinearMap.continuous_of_finiteDimensional _)

noncomputable def rowScalarActionBound (j : IntegralBasisIndex K) : ℝ :=
  Classical.choose (exists_rowKRealScalar_bound (m := m)
    (numberFieldEuclideanBasis (K := K) j))

theorem rowScalarActionBound_pos (j : IntegralBasisIndex K) :
    0 < rowScalarActionBound (m := m) j :=
  (Classical.choose_spec (exists_rowKRealScalar_bound (m := m)
    (numberFieldEuclideanBasis (K := K) j))).1

theorem rowScalarActionBound_apply (j : IntegralBasisIndex K)
    (x : RowVector K m) :
    ‖numberFieldEuclideanBasis (K := K) j • x‖ ≤
      rowScalarActionBound (m := m) j * ‖x‖ :=
  (Classical.choose_spec (exists_rowKRealScalar_bound (m := m)
    (numberFieldEuclideanBasis (K := K) j))).2 x

theorem rowScalarActionBound_apply_subtype (j : IntegralBasisIndex K)
    (x : rowRealSpan V) :
    ‖numberFieldEuclideanBasis (K := K) j • x‖ ≤
      rowScalarActionBound (m := m) j * ‖x‖ := by
  exact rowScalarActionBound_apply (m := m) j (x : RowVector K m)

theorem rowMinimaRealBasis_norm_le (i : Fin k) (j : IntegralBasisIndex K) :
    ‖rowMinimaRealBasis V ⟨i, j⟩‖ ≤
      rowScalarActionBound (m := m) j *
        ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ := by
  rw [rowMinimaRealBasis_apply, ← numberFieldEuclideanBasis_apply (K := K) j]
  exact rowScalarActionBound_apply_subtype V j
    (rowSuccessiveMinimum V i : rowRealSpan V)

noncomputable def rowScalarActionBoundSum : ℝ :=
  ∑ j : IntegralBasisIndex K, rowScalarActionBound (m := m) j

theorem rowScalarActionBound_le_sum (j : IntegralBasisIndex K) :
    rowScalarActionBound (m := m) j ≤ rowScalarActionBoundSum (K := K) (m := m) := by
  unfold rowScalarActionBoundSum
  exact Finset.single_le_sum
    (fun j _ => (rowScalarActionBound_pos (m := m) j).le)
    (Finset.mem_univ j)

theorem rowScalarActionBoundSum_nonneg :
    0 ≤ rowScalarActionBoundSum (K := K) (m := m) := by
  unfold rowScalarActionBoundSum
  exact Finset.sum_nonneg (fun j _ =>
    (rowScalarActionBound_pos (m := m) j).le)

theorem rowKRealCombinationMap_range_finrank_le {i : ℕ}
    (v : Fin i → rowZLattice V) :
    Module.finrank ℝ (LinearMap.range (rowKRealCombinationMap V v)) ≤
      i * degree K := by
  calc
    Module.finrank ℝ (LinearMap.range (rowKRealCombinationMap V v)) ≤
        Module.finrank ℝ (Fin i → K_ℝ[K]) :=
      LinearMap.finrank_range_le (rowKRealCombinationMap V v)
    _ = i * degree K := by
      rw [Module.finrank_pi_fintype]
      simp [NumberField.mixedEmbedding.euclidean.finrank, degree]

/- The dimension estimate discharges the nonemptiness condition used by the
   manuscript's recursive `K`-span definition.  If the admissible set were
   empty, every lattice vector would lie in the preceding `K`-span; since the
   lattice spans the ambient real space, that span would be all of the space,
   contradicting its dimension bound when `i < k`. -/
theorem rowSuccessiveMinimumSet_nonempty_of_lt
    (i : ℕ) (hi : i < k) :
    (successiveMinimumSet K i (rowZLattice V)
      (successiveMinimaAux K (rowZLattice V) i)).Nonempty := by
  by_contra hA
  have hprev : ∀ w : rowZLattice V,
      ((w : rowRealSpan V) ∈
        previousKSpan K (rowZLattice V) i
          (successiveMinimaAux K (rowZLattice V) i)) := by
    intro w
    by_contra hw
    apply hA
    refine ⟨w, ?_⟩
    change (w : rowRealSpan V) ∉
      previousKSpan K (rowZLattice V) i
        (successiveMinimaAux K (rowZLattice V) i)
    exact hw
  have htop := rowKRealCombinationMap_range_eq_top_of_previous_mem V
    (successiveMinimaAux K (rowZLattice V) i) hprev
  have hdim : Module.finrank ℝ (rowRealSpan V) ≤ i * degree K := by
    calc
      Module.finrank ℝ (rowRealSpan V) =
          Module.finrank ℝ
            (LinearMap.range (rowKRealCombinationMap V
              (successiveMinimaAux K (rowZLattice V) i))) := by
        rw [htop]
        simp
      _ ≤ i * degree K :=
        rowKRealCombinationMap_range_finrank_le V
          (successiveMinimaAux K (rowZLattice V) i)
  have hdim' : k * degree K ≤ i * degree K := by
    simpa [rowRealSpan_finrank V] using hdim
  have hki : k ≤ i := Nat.le_of_mul_le_mul_right hdim' Module.finrank_pos
  exact (not_le_of_gt hi) hki

theorem rowSuccessiveMinimum_mem (i : Fin k) :
    rowSuccessiveMinimum V i ∈ successiveMinimumSet K i.val
      (rowZLattice V) (successiveMinimaAux K (rowZLattice V) i.val) :=
  rowSuccessiveMinimum_mem_of_nonempty V i
    (rowSuccessiveMinimumSet_nonempty_of_lt V i.val i.isLt)

/- [derived consequence of `de:defi_of_successive`, lines 871--879] The
   recursively selected norms are nondecreasing.  This is the comparison used
   in the manuscript to bound the fundamental parallelepiped by the last
   minimum. -/
theorem rowSuccessiveMinimum_norm_le_of_index_le
    (i j : Fin k) (hij : i.val ≤ j.val) :
    ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ≤
      ‖((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V)‖ := by
  by_cases hEq : i.val = j.val
  · have hij' : i = j := Fin.ext hEq
    subst hij'
    exact le_rfl
  · have hlt : i.val < j.val := lt_of_le_of_ne hij hEq
    have hmono := previousKSpan_successiveMinimaAux_mono
      (S := K) (L := rowZLattice V) (Nat.le_of_lt hlt)
    have hmemj := rowSuccessiveMinimum_mem V j
    have hnotj :
        ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V) ∉
          previousKSpan K (rowZLattice V) j.val
            (successiveMinimaAux K (rowZLattice V) j.val) := hmemj
    have hnoti :
        ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V) ∉
          previousKSpan K (rowZLattice V) i.val
            (successiveMinimaAux K (rowZLattice V) i.val) := by
      intro hi
      exact hnotj (hmono hi)
    have hmemi : rowSuccessiveMinimum V j ∈
        successiveMinimumSet K i.val (rowZLattice V)
          (successiveMinimaAux K (rowZLattice V) i.val) := hnoti
    exact rowSuccessiveMinimum_norm_min_of_nonempty V i
      (rowSuccessiveMinimumSet_nonempty_of_lt V i.val i.isLt)
      (rowSuccessiveMinimum V j) hmemi

theorem rowSuccessiveMinimum_norm_min (i : Fin k)
    (w : rowZLattice V)
    (hw : w ∈ successiveMinimumSet K i.val (rowZLattice V)
      (successiveMinimaAux K (rowZLattice V) i.val)) :
    ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ≤
      ‖(w : rowRealSpan V)‖ :=
  rowSuccessiveMinimum_norm_min_of_nonempty V i
    (rowSuccessiveMinimumSet_nonempty_of_lt V i.val i.isLt) w hw

/- [Lean infrastructure for the manuscript's `K_ℝ · l_i` and `π_i`]
   The scalar line is represented as a real submodule so that Mathlib's
   Euclidean projection API applies.  This is only a representation of the
   manuscript's line; the admissibility condition below remains the genuine
   `K`-span from `de:defi_of_successive`. -/
noncomputable def rowKRealScalarMultiplicationMap (i : Fin k) :
    K_ℝ[K] →ₗ[ℝ] rowRealSpan V where
  toFun c := c • (rowSuccessiveMinimum V i : rowRealSpan V)
  map_add' c d := by
    exact add_smul c d (rowSuccessiveMinimum V i : rowRealSpan V)
  map_smul' r c := by
    exact smul_assoc r c (rowSuccessiveMinimum V i : rowRealSpan V)

noncomputable def rowKRealScalarLine (i : Fin k) :
    Submodule ℝ (rowRealSpan V) :=
  LinearMap.range (rowKRealScalarMultiplicationMap V i)

noncomputable def rowProjection (i : Fin k) (x : rowRealSpan V) :
    rowRealSpan V :=
  letI : CompleteSpace (rowKRealScalarLine V i) :=
    FiniteDimensional.complete ℝ (rowKRealScalarLine V i)
  (rowKRealScalarLine V i).starProjection x

/- [Lean infrastructure for `le:injective_minima`, lines 1205--1208]
   Ambient version of the line and projection occurring in the manuscript's
   definition of `π_i`.  The earlier `rowProjection` is the same projection
   computed in the row-span subtype; the bridge below proves that these are
   compatible. -/
noncomputable def rowAmbientScalarMultiplicationMap (x : RowVector K m) :
    K_ℝ[K] →ₗ[ℝ] RowVector K m where
  toFun c := c • x
  map_add' c d := by
    exact add_smul c d x
  map_smul' r c := by
    exact smul_assoc r c x

noncomputable def rowAmbientScalarLine (x : RowVector K m) :
    Submodule ℝ (RowVector K m) :=
  LinearMap.range (rowAmbientScalarMultiplicationMap (K := K) (m := m) x)

noncomputable def rowAmbientProjection (x y : RowVector K m) : RowVector K m :=
  letI : CompleteSpace
      (rowAmbientScalarLine (K := K) (m := m) x) :=
    FiniteDimensional.complete ℝ
      (rowAmbientScalarLine (K := K) (m := m) x)
  (rowAmbientScalarLine (K := K) (m := m) x).starProjection y

theorem rowKRealScalarLine_map_rowRealSpan_subtype_eq_ambient
    (i : Fin k) :
    (rowKRealScalarLine V i).map
        (rowRealSpan V).subtypeₗᵢ.toLinearMap =
      rowAmbientScalarLine (K := K) (m := m)
        (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
          RowVector K m) := by
  ext z
  constructor
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c • ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V),
      ⟨c, rfl⟩, rfl⟩

theorem rowProjection_coe_eq_rowAmbientProjection
    (i : Fin k) (j : Fin k) :
    ((rowProjection V i
        ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V) :
          rowRealSpan V) : RowVector K m) =
      rowAmbientProjection (K := K) (m := m)
        (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
          RowVector K m)
        (((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V) :
          RowVector K m) := by
  letI : CompleteSpace (rowKRealScalarLine V i) :=
    FiniteDimensional.complete ℝ (rowKRealScalarLine V i)
  letI : CompleteSpace
      (rowAmbientScalarLine (K := K) (m := m)
        (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
          RowVector K m)) :=
    FiniteDimensional.complete ℝ
      (rowAmbientScalarLine (K := K) (m := m)
        (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
          RowVector K m))
  let e : rowRealSpan V →ₗᵢ[ℝ] RowVector K m :=
    (rowRealSpan V).subtypeₗᵢ
  have he := e.map_starProjection (rowKRealScalarLine V i)
    (((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V))
  have hline := rowKRealScalarLine_map_rowRealSpan_subtype_eq_ambient V i
  have he' : e ((rowKRealScalarLine V i).starProjection
        ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V)) =
      (rowAmbientScalarLine (K := K) (m := m)
        (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
          RowVector K m)).starProjection
        (e ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V)) := by
    simpa only [e, hline] using he
  change e ((rowKRealScalarLine V i).starProjection
      ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V)) =
    (rowAmbientScalarLine (K := K) (m := m)
      (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
        RowVector K m)).starProjection
      (e ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V))
  exact he'

theorem rowProjection_mem_rowKRealScalarLine (i : Fin k) (x : rowRealSpan V) :
    rowProjection V i x ∈ rowKRealScalarLine V i := by
  letI : CompleteSpace (rowKRealScalarLine V i) :=
    FiniteDimensional.complete ℝ (rowKRealScalarLine V i)
  exact (rowKRealScalarLine V i).starProjection_apply_mem x

theorem rowSuccessiveMinimum_ne_zero (i : Fin k) :
    ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) ≠ 0 := by
  intro hzero
  have hmem := rowSuccessiveMinimum_mem V i
  change ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) ∉
      previousKSpan K (rowZLattice V) i.val
        (successiveMinimaAux K (rowZLattice V) i.val) at hmem
  apply hmem
  rw [hzero]
  exact (previousKSpan K (rowZLattice V) i.val
    (successiveMinimaAux K (rowZLattice V) i.val)).zero_mem

theorem rowSuccessiveMinimum_mem_previousKSpan_of_index_lt
    (i j : Fin k) (hij : i.val < j.val) :
    ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) ∈
      previousKSpan K (rowZLattice V) j.val
        (successiveMinimaAux K (rowZLattice V) j.val) := by
  have hmono := previousKSpan_successiveMinimaAux_mono
    (S := K) (L := rowZLattice V) (Nat.succ_le_of_lt hij)
  apply hmono
  rw [previousKSpan]
  refine Submodule.subset_span ?_
  refine ⟨⟨i.val, Nat.lt_succ_self i.val⟩, ?_⟩
  exact congrArg (fun x : rowZLattice V => (x : rowRealSpan V))
      (successiveMinimum_eq_successiveMinimaAux
      (S := K) (rowZLattice V)
      (⟨i.val, Nat.lt_succ_self i.val⟩ : Fin (i.val + 1))).symm

/- [paper: part 3 of `le:props_of_minima`, lines 977--983]
   Multiplication of a selected lattice vector by an algebraic integer stays
   in the same integral row lattice. -/
theorem rowSuccessiveMinimum_smul_integral_mem
    (i : Fin k) (a : 𝓞 K) :
    numberEmbedding K (a : K) •
        ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) ∈
      rowZLattice V := by
  change numberEmbedding K (a : K) •
      ((rowSuccessiveMinimum V i : rowZLattice V) : RowVector K m) ∈
    embeddedIntegralRowModule V
  exact embeddedIntegralRowModule_smul_integral V a
    (rowSuccessiveMinimum V i).property

/- [paper: part 3 of `le:props_of_minima`, lines 977--983]
   The integral scalar multiple also belongs to the preceding `K`-span when
   the selected vector does.  The displayed equality is the scalar-tower
   bridge from the manuscript's `K_ℝ` action to its `K`-span. -/
theorem rowSuccessiveMinimum_smul_integral_mem_previousKSpan
    (i j : Fin k) (hij : i.val < j.val) (a : 𝓞 K) :
    numberEmbedding K (a : K) •
        ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) ∈
      previousKSpan K (rowZLattice V) j.val
        (successiveMinimaAux K (rowZLattice V) j.val) := by
  have hi : ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) ∈
      previousKSpan K (rowZLattice V) j.val
        (successiveMinimaAux K (rowZLattice V) j.val) :=
    rowSuccessiveMinimum_mem_previousKSpan_of_index_lt V i j hij
  rw [show numberEmbedding K (a : K) •
      ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) =
      (a : K) • ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) by
    calc
      numberEmbedding K (a : K) •
          ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) =
          (numberEmbedding K (a : K) * 1) •
            ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) := by
        rw [mul_one]
      _ = ((a : K) • (1 : K_ℝ[K])) •
            ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) := by
        rw [kReal_smul_eq_mul]
      _ = (a : K) • ((1 : K_ℝ[K]) •
            ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)) :=
        IsScalarTower.smul_assoc (M := K) (N := K_ℝ[K])
          (α := rowRealSpan V) (a : K) (1 : K_ℝ[K])
          ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)
      _ = (a : K) •
            ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) := by
        rw [one_smul]]
  exact (previousKSpan K (rowZLattice V) j.val
    (successiveMinimaAux K (rowZLattice V) j.val)).smul_mem _ hi

noncomputable def rowSuccessiveMinimum_add_integral_smul
    (i j : Fin k) (a : 𝓞 K) : rowZLattice V :=
  ⟨((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V) +
      numberEmbedding K (a : K) •
        ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V), by
    exact (rowZLattice V).add_mem (rowSuccessiveMinimum V j).property
      (rowSuccessiveMinimum_smul_integral_mem V i a)⟩

/- [paper: part 3 of `le:props_of_minima`, lines 977--983] The preceding
   `K`-span cannot contain `l_j + α l_i`, since it already contains `l_i` and
   is closed under subtraction. -/
set_option maxHeartbeats 800000 in
theorem rowSuccessiveMinimum_add_integral_smul_not_mem_previousKSpan
    (i j : Fin k) (hij : i.val < j.val) (a : 𝓞 K) :
    ((rowSuccessiveMinimum_add_integral_smul V i j a : rowZLattice V) :
      rowRealSpan V) ∉ previousKSpan K (rowZLattice V) j.val
        (successiveMinimaAux K (rowZLattice V) j.val) := by
  intro hw
  have hai := rowSuccessiveMinimum_smul_integral_mem_previousKSpan V i j hij a
  have hsub := (previousKSpan K (rowZLattice V) j.val
    (successiveMinimaAux K (rowZLattice V) j.val)).sub_mem hw hai
  have hjmem : ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V) ∈
      previousKSpan K (rowZLattice V) j.val
        (successiveMinimaAux K (rowZLattice V) j.val) := by
    simpa [rowSuccessiveMinimum_add_integral_smul] using hsub
  exact (rowSuccessiveMinimum_mem V j) hjmem

/- [paper: part 3 of `le:props_of_minima`, lines 977--983]
   This is the manuscript's first norm comparison, before orthogonal
   decomposition: every `l_j + α l_i` is an admissible lattice vector. -/
set_option maxHeartbeats 800000 in
theorem rowSuccessiveMinimum_norm_le_of_add_integral_smul
    (i j : Fin k) (hij : i.val < j.val) (a : 𝓞 K) :
    ‖((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V)‖ ≤
      ‖((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V) +
        numberEmbedding K (a : K) •
          ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ := by
  let w := rowSuccessiveMinimum_add_integral_smul V i j a
  have hwA : w ∈ successiveMinimumSet K j.val (rowZLattice V)
      (successiveMinimaAux K (rowZLattice V) j.val) := by
    change (w : rowRealSpan V) ∉
      previousKSpan K (rowZLattice V) j.val
        (successiveMinimaAux K (rowZLattice V) j.val)
    exact rowSuccessiveMinimum_add_integral_smul_not_mem_previousKSpan V i j hij a
  have hmin := rowSuccessiveMinimum_norm_min V j w hwA
  exact hmin

/- [paper: part 3 of `le:props_of_minima`, lines 985--994]
   Orthogonal decomposition turns the preceding norm comparison into the
   corresponding comparison of the projections onto `K_ℝ l_i`. -/
set_option maxHeartbeats 800000 in
theorem rowProjection_norm_le_of_add_integral_smul
    (i j : Fin k) (hij : i.val < j.val) (a : 𝓞 K) :
    ‖rowProjection V i
        ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V)‖ ≤
      ‖rowProjection V i
          ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V) +
        numberEmbedding K (a : K) •
          ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ := by
  letI : CompleteSpace (rowKRealScalarLine V i) :=
    FiniteDimensional.complete ℝ (rowKRealScalarLine V i)
  let x : rowRealSpan V :=
    ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V)
  let s : rowRealSpan V :=
    numberEmbedding K (a : K) •
      ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)
  have hs : s ∈ rowKRealScalarLine V i := by
    change numberEmbedding K (a : K) •
        ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) ∈
      LinearMap.range (rowKRealScalarMultiplicationMap V i)
    exact ⟨numberEmbedding K (a : K), rfl⟩
  have hmin : ‖x‖ ≤ ‖x + s‖ := by
    exact rowSuccessiveMinimum_norm_le_of_add_integral_smul V i j hij a
  have hproj_add :
      (rowKRealScalarLine V i).starProjection (x + s) =
        (rowKRealScalarLine V i).starProjection x + s := by
    rw [map_add, (rowKRealScalarLine V i).starProjection_eq_self_iff.mpr hs]
  have hsorth : s ∈ (rowKRealScalarLine V i)ᗮᗮ :=
    (rowKRealScalarLine V i).le_orthogonal_orthogonal hs
  have hsorth_zero :
      ((rowKRealScalarLine V i)ᗮ).starProjection s = 0 :=
    ((rowKRealScalarLine V i)ᗮ).starProjection_apply_eq_zero_iff.mpr hsorth
  have horth_add :
      ((rowKRealScalarLine V i)ᗮ).starProjection (x + s) =
        ((rowKRealScalarLine V i)ᗮ).starProjection x := by
    rw [map_add, hsorth_zero, add_zero]
  have hsq : ‖x‖ ^ 2 ≤ ‖x + s‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hmin
  have hpy_x := (rowKRealScalarLine V i).norm_sq_eq_add_norm_sq_starProjection x
  have hpy_add :=
    (rowKRealScalarLine V i).norm_sq_eq_add_norm_sq_starProjection (x + s)
  rw [horth_add] at hpy_add
  have hsq_proj :
      ‖(rowKRealScalarLine V i).starProjection x‖ ^ 2 ≤
        ‖(rowKRealScalarLine V i).starProjection (x + s)‖ ^ 2 := by
    nlinarith [hpy_x, hpy_add, hsq]
  have hnorm := (sq_le_sq₀
    (norm_nonneg ((rowKRealScalarLine V i).starProjection x))
    (norm_nonneg ((rowKRealScalarLine V i).starProjection (x + s)))).mp hsq_proj
  change ‖(rowKRealScalarLine V i).starProjection x‖ ≤
    ‖(rowKRealScalarLine V i).starProjection x + s‖
  rw [← hproj_add]
  exact hnorm

/- [derived consequence of part 3 of `le:props_of_minima`, lines 975--1002]
   The coefficient approximation in the fixed number-field lattice supplies
   the uniform constant in the manuscript's `c_{ij}` bound. -/
set_option maxHeartbeats 800000 in
theorem rowProjection_norm_le_of_successiveMinima
    (i j : Fin k) (hij : i.val < j.val) :
    ‖rowProjection V i
        ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V)‖ ≤
      rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K *
        ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ := by
  letI : CompleteSpace (rowKRealScalarLine V i) :=
    FiniteDimensional.complete ℝ (rowKRealScalarLine V i)
  have hp := rowProjection_mem_rowKRealScalarLine V i
    ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V)
  change rowProjection V i
      ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V) ∈
    LinearMap.range (rowKRealScalarMultiplicationMap V i) at hp
  rcases hp with ⟨c, hc⟩
  obtain ⟨a, ha⟩ := exists_numberField_coefficient_approx (K := K) (-c)
  have hac : ‖c + numberEmbedding K (a : K)‖ ≤
      numberFieldCoefficientRadius K := by
    calc
      ‖c + numberEmbedding K (a : K)‖ =
          ‖-(c + numberEmbedding K (a : K))‖ := by rw [norm_neg]
      _ = ‖-c - numberEmbedding K (a : K)‖ := by congr 1 <;> abel
      _ ≤ numberFieldCoefficientRadius K := ha
  have hproj := rowProjection_norm_le_of_add_integral_smul V i j hij a
  have hscalar :
      rowProjection V i
          ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V) +
        numberEmbedding K (a : K) •
          ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) =
      (c + numberEmbedding K (a : K)) •
        ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) := by
    rw [← hc]
    change c • ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) +
      numberEmbedding K (a : K) •
        ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) = _
    rw [add_smul]
  rw [hscalar] at hproj
  calc
    ‖rowProjection V i
        ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V)‖ ≤
        ‖(c + numberEmbedding K (a : K)) •
          ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ := hproj
    _ ≤ rowKRealSmulBound (K := K) (m := m) *
          ‖c + numberEmbedding K (a : K)‖ *
            ‖((rowSuccessiveMinimum V i : rowZLattice V) : RowVector K m)‖ := by
      exact rowKRealSmulBound_apply (K := K) (m := m)
        (c + numberEmbedding K (a : K))
        ((rowSuccessiveMinimum V i : rowZLattice V) : RowVector K m)
    _ ≤ rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K *
            ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ := by
      have hnorm :
          ‖((rowSuccessiveMinimum V i : rowZLattice V) : RowVector K m)‖ =
            ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ := rfl
      rw [hnorm]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hac
          (rowKRealSmulBound_pos (K := K) (m := m)).le)
        (norm_nonneg _)

/- [Lean infrastructure for `le:injective_minima`, lines 1205--1208]
   The selected lattice point is represented internally by the subtype
   `rowZLattice V`.  This choice recovers its manuscript row in
   `M_{1 × m}(𝓞_K)`; the following equality is the proved embedding bridge. -/
noncomputable def rowSuccessiveMinimumIntegralRow (i : Fin k) :
    Fin m → 𝓞 K :=
  Classical.choose ((mem_embeddedIntegralRowModule_iff V
      (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
        RowVector K m)).1 (by
    change (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
      RowVector K m) ∈ embeddedIntegralRowModule V
    exact (rowSuccessiveMinimum V i).property))

theorem integralVectorEmbedding_rowSuccessiveMinimumIntegralRow (i : Fin k) :
    integralVectorEmbedding (K := K) m
        (rowSuccessiveMinimumIntegralRow V i) =
      (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
        RowVector K m) := by
  exact Classical.choose_spec ((mem_embeddedIntegralRowModule_iff V
      (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
        RowVector K m)).1 (by
    change (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
      RowVector K m) ∈ embeddedIntegralRowModule V
    exact (rowSuccessiveMinimum V i).property)) |>.2

/- [paper, definition in `le:injective_minima`, lines 1203--1208]
   Exact Lean encoding of the manuscript's
   `𝓑_k^(C)(T)`.  Rows are stored as elements of `𝓞_K^m`, and every norm and
   projection is applied after the fixed Minkowski embedding. -/
noncomputable def possibleSuccessiveMinimaSet (C T : ℝ) :
    Set (Fin k → Fin m → 𝓞 K) :=
  {l | (∀ i j : Fin k, i.val ≤ j.val →
      ‖integralVectorEmbedding (K := K) m (l i)‖ ≤
        ‖integralVectorEmbedding (K := K) m (l j)‖) ∧
    (∀ i : Fin k,
      ‖integralVectorEmbedding (K := K) m (l i)‖ ≤ C * T) ∧
    (∀ i j : Fin k, i.val < j.val →
      ‖rowAmbientProjection (K := K) (m := m)
          (integralVectorEmbedding (K := K) m (l i))
          (integralVectorEmbedding (K := K) m (l j))‖ ≤
        C * ‖integralVectorEmbedding (K := K) m (l i)‖)}

/- [derived consequence of paper `le:injective_minima`, lines 1199--1208]
   The manuscript's bounded tuple set `𝓑_k^(C)(T)` is finite.  The proof
   deliberately retains its rows as elements of `𝓞_K^m`: each coordinate row
   maps injectively into the fixed ambient integral-row lattice, whose bounded
   balls are finite. -/
theorem finite_possibleSuccessiveMinimaSet
    {C T : ℝ} :
    (possibleSuccessiveMinimaSet (K := K) (m := m) (k := k) C T).Finite := by
  let L : Submodule ℤ (RowVector K m) :=
    ambientIntegralRowModule (K := K) m
  let e : (Fin m → 𝓞 K) → L := fun x =>
    ⟨integralVectorEmbedding (K := K) m x,
      integralVectorEmbedding_mem_ambientIntegralRowModule (K := K) m x⟩
  have he : Function.Injective e := by
    intro x y hxy
    apply integralVectorEmbedding_injective (K := K) m
    exact congrArg Subtype.val hxy
  have hball : Set.Finite {v : L | ‖(v : RowVector K m)‖ ≤ C * T} := by
    exact lattice_ball_finite L
  have hrows : Set.Finite {x : Fin m → 𝓞 K |
      ‖integralVectorEmbedding (K := K) m x‖ ≤ C * T} := by
    have hpre := hball.preimage he.injOn
    simpa [e, L] using hpre
  have htuples : Set.Finite {l : Fin k → Fin m → 𝓞 K |
      ∀ i, ‖integralVectorEmbedding (K := K) m (l i)‖ ≤ C * T} := by
    simpa using (Set.Finite.pi' fun _ : Fin k => hrows)
  apply htuples.subset
  intro l hl
  exact hl.2.1

/- [paper, part 1 of `le:injective_minima`, lines 1211--1225] The minima
   tuple satisfies the defining conditions of `𝓑_k^(C)(T)` once `C` dominates
   the projection constant and the last minimum has the asserted cutoff. -/
set_option maxHeartbeats 800000 in
theorem rowSuccessiveMinimumIntegralTuple_mem_possibleSuccessiveMinimaSet
    {C T : ℝ} (hk : 0 < k) (hCproj :
      rowKRealSmulBound (K := K) (m := m) * numberFieldCoefficientRadius K ≤ C)
    (hlast :
      ‖((rowSuccessiveMinimum V ⟨k - 1, Nat.pred_lt hk.ne'⟩ : rowZLattice V) :
        rowRealSpan V)‖ ≤ C * T) :
    (rowSuccessiveMinimumIntegralRow V) ∈
      possibleSuccessiveMinimaSet (K := K) (m := m) C T := by
  have hemb (i : Fin k) :
      integralVectorEmbedding (K := K) m
          (rowSuccessiveMinimumIntegralRow V i) =
        (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
          RowVector K m) :=
    integralVectorEmbedding_rowSuccessiveMinimumIntegralRow V i
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    rw [hemb i, hemb j]
    exact rowSuccessiveMinimum_norm_le_of_index_le V i j hij
  · intro i
    rw [hemb i]
    have hi_last : i.val ≤ k - 1 := (Nat.le_sub_one_iff_lt hk).2 i.isLt
    exact (rowSuccessiveMinimum_norm_le_of_index_le V i
      ⟨k - 1, Nat.pred_lt hk.ne'⟩ hi_last).trans hlast
  · intro i j hij
    rw [hemb i, hemb j]
    rw [← rowProjection_coe_eq_rowAmbientProjection V i j]
    have hproj := rowProjection_norm_le_of_successiveMinima V i j hij
    calc
      ‖((rowProjection V i
          ((rowSuccessiveMinimum V j : rowZLattice V) : rowRealSpan V) :
            rowRealSpan V) : RowVector K m)‖ ≤
          rowKRealSmulBound (K := K) (m := m) *
            numberFieldCoefficientRadius K *
              ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ :=
        hproj
      _ ≤ C *
          ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ := by
        exact mul_le_mul_of_nonneg_right hCproj (norm_nonneg _)

/- [derived consequence of part 1 of `le:props_of_minima`, lines 1130--1154]
   This is the arithmetic lower-height step in the manuscript.  `δ` is the
   fixed positive lower bound for nonzero integral rows, `Ccut` is the paper's
   factor `k^(-1/2) C{sup}`, and `hprod` is the product estimate supplied by
   the cited geometry-of-numbers input.  The separate hypotheses expose the
   two interfaces used by the paper instead of hiding either one. -/
set_option maxHeartbeats 800000 in
theorem rowSpaceHeight_lower_bound_of_minima
    (d : ℕ) (hd : 0 < d) (hk : 0 < k)
    {δ Ccut Cprod T : ℝ}
    (hδ : 0 < δ) (hCcut : 0 < Ccut) (hCprod : 0 < Cprod) (hT : 0 < T)
    (hmin : ∀ i : Fin k,
      δ ≤ ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖)
    (hlast : Ccut * T ≤
      ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ : rowZLattice V) :
        rowRealSpan V)‖)
    (hprod : (∏ i : Fin k,
        ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^ d) ≤
      Cprod * rowSpaceHeight V) :
    (((δ ^ (k - 1) * Ccut) ^ d) / Cprod) * T ^ d ≤ rowSpaceHeight V := by
  let last : Fin k := ⟨k - 1, by omega⟩
  have hrest :
      (∏ i ∈ (Finset.univ.erase last), δ ^ d) ≤
        ∏ i ∈ (Finset.univ.erase last),
          ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^ d := by
    apply Finset.prod_le_prod
    · intro i hi
      exact pow_nonneg hδ.le d
    · intro i hi
      exact pow_le_pow_left₀ hδ.le (hmin i) d
  have hlast_pow :
      (Ccut * T) ^ d ≤
        ‖((rowSuccessiveMinimum V last : rowZLattice V) : rowRealSpan V)‖ ^ d :=
    pow_le_pow_left₀ (mul_nonneg hCcut.le hT.le) hlast d
  have hprod_lower :
      (∏ i ∈ (Finset.univ.erase last), δ ^ d) * (Ccut * T) ^ d ≤
        ∏ i : Fin k,
          ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^ d := by
    calc
      (∏ i ∈ (Finset.univ.erase last), δ ^ d) * (Ccut * T) ^ d ≤
          (∏ i ∈ (Finset.univ.erase last),
            ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^ d) *
            (Ccut * T) ^ d :=
        mul_le_mul_of_nonneg_right hrest (pow_nonneg (mul_nonneg hCcut.le hT.le) d)
      _ ≤ (∏ i ∈ (Finset.univ.erase last),
            ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^ d) *
            ‖((rowSuccessiveMinimum V last : rowZLattice V) : rowRealSpan V)‖ ^ d :=
        mul_le_mul_of_nonneg_left hlast_pow (Finset.prod_nonneg fun i hi =>
          pow_nonneg (norm_nonneg _) d)
      _ = ∏ i : Fin k,
          ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^ d := by
        exact Finset.prod_erase_mul
          (s := (Finset.univ : Finset (Fin k)))
          (f := fun i : Fin k =>
            ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^ d)
          (Finset.mem_univ last)
  have hfactor :
      ((δ ^ (k - 1) * Ccut) ^ d) * T ^ d =
        (∏ i ∈ (Finset.univ.erase last), δ ^ d) * (Ccut * T) ^ d := by
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ last),
      Finset.card_univ]
    simp only [Fintype.card_fin]
    calc
      ((δ ^ (k - 1) * Ccut) ^ d) * T ^ d =
          (δ ^ (k - 1)) ^ d * Ccut ^ d * T ^ d := by
            rw [mul_pow]
      _ = (δ ^ d) ^ (k - 1) * Ccut ^ d * T ^ d := by
            rw [← pow_mul, Nat.mul_comm, pow_mul]
      _ = (δ ^ d) ^ (k - 1) * (Ccut * T) ^ d := by
            rw [mul_pow]
            ring
  have hmain :
      ((δ ^ (k - 1) * Ccut) ^ d) * T ^ d ≤ Cprod * rowSpaceHeight V := by
    rw [hfactor]
    exact hprod_lower.trans hprod
  have hdiv :
      (((δ ^ (k - 1) * Ccut) ^ d) * T ^ d) / Cprod ≤ rowSpaceHeight V :=
    (div_le_iff₀ hCprod).2 (by simpa [mul_comm] using hmain)
  calc
    (((δ ^ (k - 1) * Ccut) ^ d) / Cprod) * T ^ d =
        (((δ ^ (k - 1) * Ccut) ^ d) * T ^ d) / Cprod := by ring
    _ ≤ rowSpaceHeight V := hdiv

/- [derived consequence of part 2 of `le:props_of_minima`, lines 936--983]
   The fixed integral basis and the monotonicity of the selected minima give
   the paper's covering-radius conclusion with an explicit constant. -/
theorem rowCoveringRadius_le_of_successiveMinima
    (hk : 0 < k) :
    latticeCoveringRadius (rowZLattice V) ≤
      (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
          rowScalarActionBoundSum (K := K) (m := m) *
        ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ : rowZLattice V) :
          rowRealSpan V)‖ := by
  let last : Fin k := ⟨k - 1, by omega⟩
  have hmem : ∀ q : Σ _ : Fin k, IntegralBasisIndex K,
      rowMinimaRealBasis V q ∈ rowZLattice V := by
    rintro ⟨i, j⟩
    exact rowMinimaRealBasis_mem_rowZLattice V i j
  have hcover := latticeCoveringRadius_le_sum_of_real_basis
    (L := rowZLattice V) (rowMinimaRealBasis V) hmem
  have hsum :
      (∑ q : Σ _ : Fin k, IntegralBasisIndex K,
        ‖rowMinimaRealBasis V q‖) ≤
        ∑ _q : Σ _ : Fin k, IntegralBasisIndex K,
          rowScalarActionBoundSum (K := K) (m := m) *
            ‖((rowSuccessiveMinimum V last : rowZLattice V) : rowRealSpan V)‖ := by
    apply Finset.sum_le_sum
    intro q hq
    rcases q with ⟨i, j⟩
    have hli :
        ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ≤
          ‖((rowSuccessiveMinimum V last : rowZLattice V) : rowRealSpan V)‖ :=
      rowSuccessiveMinimum_norm_le_of_index_le V i last (by
        dsimp [last]
        omega)
    calc
      ‖rowMinimaRealBasis V ⟨i, j⟩‖ ≤
          rowScalarActionBound (m := m) j *
            ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ :=
        rowMinimaRealBasis_norm_le V i j
      _ ≤ rowScalarActionBoundSum (K := K) (m := m) *
            ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ :=
        mul_le_mul_of_nonneg_right (rowScalarActionBound_le_sum (K := K) (m := m) j)
          (norm_nonneg _)
      _ ≤ rowScalarActionBoundSum (K := K) (m := m) *
            ‖((rowSuccessiveMinimum V last : rowZLattice V) : rowRealSpan V)‖ :=
        mul_le_mul_of_nonneg_left hli
          (rowScalarActionBoundSum_nonneg (K := K) (m := m))
  calc
    latticeCoveringRadius (rowZLattice V) ≤
        ∑ q : Σ _ : Fin k, IntegralBasisIndex K,
          ‖rowMinimaRealBasis V q‖ := hcover
    _ ≤ ∑ _q : Σ _ : Fin k, IntegralBasisIndex K,
          rowScalarActionBoundSum (K := K) (m := m) *
            ‖((rowSuccessiveMinimum V last : rowZLattice V) : rowRealSpan V)‖ := hsum
    _ = (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
          rowScalarActionBoundSum (K := K) (m := m) *
        ‖((rowSuccessiveMinimum V last : rowZLattice V) : rowRealSpan V)‖ := by
      rw [Finset.sum_const]
      simp only [Finset.card_univ, nsmul_eq_mul]
      ring

/- [derived consequence of `le:props_of_minima` and equation
   `eq:just_as_before`, lines 920--983 and 1730--1738] The covering-radius
   bound and the cited product-of-minima estimate give the pointwise summand
   comparison used before the injection into `𝓑_k(T)`.  The product estimate
   is deliberately an explicit hypothesis: in the paper it is the input
   attributed to Fieker--Stehlé, Theorem 2. -/
set_option maxHeartbeats 1200000 in
theorem rowCoveringRadius_div_height_pow_le_successiveMinimumWeight
    (n : ℕ) (hk : 0 < k) {Cprod : ℝ}
    (hprod : (∏ i : Fin k,
        ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^
          degree K) ≤ Cprod * rowSpaceHeight V) :
    latticeCoveringRadius (rowZLattice V) / (rowSpaceHeight V) ^ n ≤
      (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
          rowScalarActionBoundSum (K := K) (m := m) * Cprod ^ n *
        ((∏ i : Fin k,
          ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^
            degree K)⁻¹) ^ n *
          ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ :
            rowZLattice V) : rowRealSpan V)‖ := by
  let last : Fin k := ⟨k - 1, by omega⟩
  let P : ℝ := ∏ i : Fin k,
    ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^ degree K
  let R : ℝ := (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
    rowScalarActionBoundSum (K := K) (m := m)
  let L : ℝ := ‖((rowSuccessiveMinimum V last : rowZLattice V) :
    rowRealSpan V)‖
  have hminimum_ne (i : Fin k) :
      ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) ≠ 0 := by
    intro hi
    apply rowSuccessiveMinimum_ne_zero V i
    apply Subtype.ext
    exact congrArg Subtype.val hi
  have hPpos : 0 < P := by
    apply Finset.prod_pos
    intro i hi
    exact pow_pos (norm_pos_iff.mpr (hminimum_ne i)) _
  have hheight : 0 < rowSpaceHeight V := rowSpaceHeight_pos V
  have hprod' : P ≤ Cprod * rowSpaceHeight V := hprod
  have hinv : (rowSpaceHeight V)⁻¹ ≤ Cprod * P⁻¹ := by
    calc
      (rowSpaceHeight V)⁻¹ = 1 / rowSpaceHeight V := (one_div _).symm
      _ ≤ Cprod / P :=
        (div_le_div_iff₀ hheight hPpos).2 (by simpa using hprod')
      _ = Cprod * P⁻¹ := div_eq_mul_inv _ _
  have hinvpow : (rowSpaceHeight V)⁻¹ ^ n ≤ Cprod ^ n * P⁻¹ ^ n := by
    calc
      (rowSpaceHeight V)⁻¹ ^ n ≤ (Cprod * P⁻¹) ^ n :=
        pow_le_pow_left₀ (inv_nonneg.mpr hheight.le) hinv n
      _ = Cprod ^ n * P⁻¹ ^ n := by rw [mul_pow]
  have hcover : latticeCoveringRadius (rowZLattice V) ≤ R * L :=
    rowCoveringRadius_le_of_successiveMinima V hk
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg (Nat.cast_nonneg _)
      (rowScalarActionBoundSum_nonneg (K := K) (m := m))
  have hLnonneg : 0 ≤ L := norm_nonneg _
  calc
    latticeCoveringRadius (rowZLattice V) / (rowSpaceHeight V) ^ n =
        latticeCoveringRadius (rowZLattice V) *
          (rowSpaceHeight V)⁻¹ ^ n := by
      rw [div_eq_mul_inv, inv_pow]
    _ ≤ (R * L) * (rowSpaceHeight V)⁻¹ ^ n :=
      mul_le_mul_of_nonneg_right hcover
        (pow_nonneg (inv_nonneg.mpr hheight.le) _)
    _ ≤ (R * L) * (Cprod ^ n * P⁻¹ ^ n) :=
      mul_le_mul_of_nonneg_left hinvpow (mul_nonneg hRnonneg hLnonneg)
    _ = R * Cprod ^ n * P⁻¹ ^ n * L := by ring
    _ = (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
          rowScalarActionBoundSum (K := K) (m := m) * Cprod ^ n *
        ((∏ i : Fin k,
          ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^
            degree K)⁻¹) ^ n *
          ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ :
            rowZLattice V) : rowRealSpan V)‖ := by
      rfl

/- This is the direction needed to replace the recursively selected
   manuscript minimum by the corresponding module minimum in the product
   estimate cited at [FD10, Theorem 2]. -/
theorem rowSuccessiveMinimum_norm_le_moduleMinimum (i : Fin k) :
    ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ≤
      moduleMinimum (K := K) (rowZLattice V) i := by
  have hfull : Module.finrank K
      (Submodule.span K (rowZLattice V : Set (rowRealSpan V))) = k :=
    rowZLattice_K_span_finrank V
  have hprev := successiveMinimaAux_linearIndependent_of_finrank
    (E := rowRealSpan V) (K := K) k (rowZLattice V) hfull i.val
      (Nat.le_of_lt i.isLt)
  change ‖((successiveMinimum K (rowZLattice V) i : rowZLattice V) :
      rowRealSpan V)‖ ≤ moduleMinimum (K := K) (rowZLattice V) i
  exact successiveMinimum_norm_le_moduleMinimum
    (K := K) (L := rowZLattice V) i
    (rowSuccessiveMinimumSet_nonempty_of_lt V i.val i.isLt) hprev

/- [paper, proof of `le:injective_minima`, lines 1221--1225] If a bounded
   lattice set contains `k` independent vectors, the last selected minimum is
   bounded by the same radius.  The hypothesis is stated on the paper's
   lattice `Λ_D`; extracting the bounded independent rows from `D ∈ 𝓕_k(T)` is
   a separate matrix-rank bridge in `MainTheorems`. -/
theorem rowSuccessiveMinimum_last_norm_le_of_independent_bounded
    (hk : 0 < k) {R : ℝ}
    (hV : ∃ v : Fin k → rowZLattice V,
      LinearIndependent K (fun i =>
        ((v i : rowZLattice V) : rowRealSpan V)) ∧
      ∀ i, ‖((v i : rowZLattice V) : rowRealSpan V)‖ ≤ R) :
    ‖((rowSuccessiveMinimum V ⟨k - 1, Nat.pred_lt hk.ne'⟩ :
        rowZLattice V) : rowRealSpan V)‖ ≤ R := by
  obtain ⟨v, hvLI, hv⟩ := hV
  let e : Fin (k - 1 + 1) → Fin k := fun i =>
    ⟨i.val, by omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin k => x.val) hij
  let v' : Fin (k - 1 + 1) → rowZLattice V := v ∘ e
  have hv'LI : LinearIndependent K (fun i =>
      ((v' i : rowZLattice V) : rowRealSpan V)) := by
    change LinearIndependent K
      ((fun i => ((v i : rowZLattice V) : rowRealSpan V)) ∘ e)
    exact hvLI.comp e he
  have hv' : ∀ i, ‖((v' i : rowZLattice V) : rowRealSpan V)‖ ≤ R := by
    intro i
    exact hv (e i)
  let last : Fin k := ⟨k - 1, Nat.pred_lt hk.ne'⟩
  have hmin := rowSuccessiveMinimum_norm_le_moduleMinimum V last
  have hmodule := moduleMinimum_le_sup_norm_of_linearIndependent
    (K := K) (rowZLattice V) (i := last) v' hv'LI
  have hsup : (Finset.univ.sup' (Finset.univ_nonempty :
      (Finset.univ : Finset (Fin (last.val + 1))).Nonempty)
      (fun i => ‖((v' i : rowZLattice V) : rowRealSpan V)‖)) ≤ R := by
    apply Finset.sup'_le
      (Finset.univ_nonempty : (Finset.univ : Finset (Fin (last.val + 1))).Nonempty)
      (fun i => ‖((v' i : rowZLattice V) : rowRealSpan V)‖)
    intro i hi
    exact hv' i
  change ‖((rowSuccessiveMinimum V last : rowZLattice V) : rowRealSpan V)‖ ≤ R
  exact hmin.trans (hmodule.trans hsup)

/- [cited input] Fieker--Stehlé, *Short Bases of Lattices over Number Fields*
   (ANTS-IX, 2010), Theorem 2, p. 3, proves the product bound under its
   `T₂` norm.  The paper's norm (equation `eq:norm`, lines 661--674) includes
   a discriminant/trace normalization, while the present `RowVector` uses
   Mathlib's unscaled Euclidean mixed space.  For fixed `K` the two norms and
   covolumes differ by fixed positive factors, so the manuscript needs only
   the uniform constant recorded below.  A proved normalization bridge from
   the source theorem to this proposition is still required.  The module in
   the source is `Λ_D = V ∩ 𝓞_K^m`, represented by `rowZLattice V`.
   This is a proposition, not an axiom, instance, or replacement proof. -/
def FiekerStehleProductBound (K : Type*) [Field K] [NumberField K]
    (m k : ℕ) (C : ℝ) : Prop :=
  ∀ V : Grassmannian K m k, 0 < k →
    (∏ i : Fin k, moduleMinimum (K := K) (rowZLattice V) i) ≤
      C * (rowSpaceHeight V) ^ (1 / (degree K : ℝ))

/- [derived consequence] For rank one, the product assertion used from
   Fieker--Stehlé is already a consequence of the first Minkowski theorem
   formalized above: a nonzero lattice vector is a one-element
   `K`-linearly-independent family.  This proves the local, raw-Mathlib-metric
   rank-one interface; the separate normalization bridge to the manuscript's
   discriminant/trace metric remains recorded in
   `notes/formalization-issues.md`. -/
theorem moduleMinimum_zero_le_firstMinkowski
    {m : ℕ} (V : Grassmannian K m 1) :
    moduleMinimum (K := K) (rowZLattice V) (0 : Fin 1) ≤
      minkowskiConstant (E := rowRealSpan V) *
        (rowSpaceHeight V) ^ (1 / (degree K : ℝ)) := by
  letI : Nontrivial (rowRealSpan V) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [rowRealSpan_finrank V]
    exact Nat.mul_pos (by omega) Module.finrank_pos
  obtain ⟨w, hw, hbound⟩ :=
    exists_nonzero_latticeVector_norm_le_covolume_rpow (rowZLattice V)
  let v : Fin ((0 : Fin 1).val + 1) → rowZLattice V := fun _ => w
  letI : Subsingleton (Fin ((0 : Fin 1).val + 1)) :=
    ⟨fun a b => Fin.ext (by omega)⟩
  have hw' : ((v 0 : rowZLattice V) : rowRealSpan V) ≠ 0 := by
    intro hzero
    apply hw
    exact Subtype.ext hzero
  have hv : LinearIndependent K (fun j =>
      ((v j : rowZLattice V) : rowRealSpan V)) := by
    exact LinearIndependent.of_subsingleton 0 hw'
  have hminimum := moduleMinimum_le_sup_norm_of_linearIndependent
    (K := K) (rowZLattice V) (0 : Fin 1) v hv
  calc
    moduleMinimum (K := K) (rowZLattice V) (0 : Fin 1) ≤
        Finset.univ.sup' (Finset.univ_nonempty :
          (Finset.univ : Finset (Fin ((0 : Fin 1).val + 1))).Nonempty)
          (fun j => ‖((v j : rowZLattice V) : rowRealSpan V)‖) := hminimum
    _ = ‖((w : rowZLattice V) : rowRealSpan V)‖ := by
      apply Finset.sup'_eq_of_forall
      intro j _
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rfl
    _ ≤ minkowskiConstant (E := rowRealSpan V) *
        (ZLattice.covolume (rowZLattice V)
          (volume : Measure (rowRealSpan V))) ^
          (1 / (Module.finrank ℝ (rowRealSpan V) : ℝ)) := hbound
    _ = minkowskiConstant (E := rowRealSpan V) *
        (rowSpaceHeight V) ^ (1 / (degree K : ℝ)) := by
      rw [← rowSpaceHeight_eq_volume_covolume V, rowRealSpan_finrank V]
      norm_num

/- [derived consequence] This packages the preceding rank-one proof into the
   same explicitly named interface as the cited Fieker--Stehlé theorem.  It
   is only the rank-one case, not a claim to have formalized the source's
   all-rank Theorem 2. -/
theorem exists_fiekerStehleProductBound_rank_one
    (m : ℕ) : ∃ C : ℝ, 0 < C ∧ FiekerStehleProductBound K m 1 C := by
  letI : Nonempty (Fin (degree K)) :=
    ⟨⟨0, Module.finrank_pos⟩⟩
  letI : Nontrivial (EuclideanSpace ℝ (Fin (degree K))) := by
    infer_instance
  refine ⟨minkowskiConstant (E := EuclideanSpace ℝ (Fin (degree K))),
    minkowskiConstant_pos, ?_⟩
  intro V _
  letI : Nontrivial (rowRealSpan V) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [rowRealSpan_finrank V]
    exact Nat.mul_pos (by omega) Module.finrank_pos
  have hmin := moduleMinimum_zero_le_firstMinkowski V
  have hdimension : Module.finrank ℝ (rowRealSpan V) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (degree K))) := by
    rw [rowRealSpan_finrank V]
    simp
  have hconstant : minkowskiConstant (E := rowRealSpan V) =
      minkowskiConstant (E := EuclideanSpace ℝ (Fin (degree K))) :=
    minkowskiConstant_eq_of_finrank_eq (E := rowRealSpan V) hdimension
  simpa [FiekerStehleProductBound, hconstant] using hmin

/- [cited input] This packages the uniform-in-`V` consequence needed from
   Fieker--Stehlé Theorem 2 after the normalization bridge described above.
   The constant may depend on the fixed field and the ambient/rank parameters,
   as the manuscript permits, but not on `V`. -/
def HasFiekerStehleProductBound (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ m k : ℕ, ∃ C : ℝ, 0 < C ∧ FiekerStehleProductBound K m k C

/- [derived consequence] This is the exact exponent conversion from
   Fieker--Stehlé Theorem 2 to the product form used in part 1 of
   `le:props_of_minima` (papers/katznelson.tex, lines 924--934).  It uses only
   the cited statement above, positivity of the height, and
   `degree K > 0`; in particular it introduces no new geometry-of-numbers
   assertion. -/
theorem moduleMinimum_prod_pow_le_of_fiekerStehle
    {m k : ℕ} (V : Grassmannian K m k) (C : ℝ) (hk : 0 < k)
    (hFS : FiekerStehleProductBound K m k C) :
    (∏ i : Fin k, (moduleMinimum (K := K) (rowZLattice V) i) ^ degree K) ≤
      C ^ degree K * rowSpaceHeight V := by
  let P : ℝ := ∏ i : Fin k, moduleMinimum (K := K) (rowZLattice V) i
  have hP : 0 ≤ P := by
    dsimp [P]
    apply Finset.prod_nonneg
    intro i hi
    exact (norm_nonneg _).trans
      (rowSuccessiveMinimum_norm_le_moduleMinimum V i)
  have hpow : P ^ degree K ≤
      (C * (rowSpaceHeight V) ^ (1 / (degree K : ℝ))) ^ degree K := by
    exact pow_le_pow_left₀ hP (hFS V hk) _
  have hdegree : degree K ≠ 0 := Nat.ne_of_gt Module.finrank_pos
  have hheight : 0 ≤ rowSpaceHeight V := (rowSpaceHeight_pos V).le
  calc
    (∏ i : Fin k, (moduleMinimum (K := K) (rowZLattice V) i) ^ degree K) =
        P ^ degree K := by
      simp [P, Finset.prod_pow]
    _ ≤ (C * (rowSpaceHeight V) ^ (1 / (degree K : ℝ))) ^ degree K := hpow
    _ = C ^ degree K * rowSpaceHeight V := by
      rw [mul_pow]
      congr 1
      simpa [one_div] using
        (Real.rpow_inv_natCast_pow hheight hdegree)

/- [derived consequence] The following general assembly statement is used
   when the cited product estimate is supplied in a different but proved
   normalization. -/
theorem rowSuccessiveMinimum_prod_norm_pow_le_of_moduleMinimum_bound
    (C : ℝ)
    (hmodule :
      (∏ i : Fin k, (moduleMinimum (K := K) (rowZLattice V) i) ^ degree K) ≤
        C * rowSpaceHeight V) :
    (∏ i : Fin k,
        ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^
          degree K) ≤ C * rowSpaceHeight V := by
  calc
    (∏ i : Fin k,
        ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^
          degree K) ≤
        ∏ i : Fin k, (moduleMinimum (K := K) (rowZLattice V) i) ^
          degree K := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact pow_le_pow_left₀ (norm_nonneg _)
          (rowSuccessiveMinimum_norm_le_moduleMinimum V i) _
    _ ≤ C * rowSpaceHeight V := hmodule

/- [derived consequence] Combining the exact Fieker--Stehlé conversion with
   the proved comparison from the manuscript's recursive minima to module
   minima gives the displayed product estimate in `le:props_of_minima`.
   This theorem is conditional on the visibly named cited input above, so it
   cannot be mistaken for a local proof of Fieker--Stehlé Theorem 2. -/
theorem rowSuccessiveMinimum_prod_norm_pow_le_of_fiekerStehle
    {m k : ℕ} (V : Grassmannian K m k) (C : ℝ) (hk : 0 < k)
    (hFS : FiekerStehleProductBound K m k C) :
    (∏ i : Fin k,
        ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^
          degree K) ≤
      C ^ degree K * rowSpaceHeight V := by
  apply rowSuccessiveMinimum_prod_norm_pow_le_of_moduleMinimum_bound V
  exact moduleMinimum_prod_pow_le_of_fiekerStehle V C hk hFS

/- [derived consequence] This selects one constant uniformly for all
   rank-`k` row spaces and is exactly the `C^{okhadamard}`-style product
   interface consumed by the manuscript's later estimates. -/
theorem exists_rowSuccessiveMinimum_prod_norm_pow_le_of_fiekerStehle
    {m k : ℕ} (hk : 0 < k) (hFS : HasFiekerStehleProductBound K) :
    ∃ Cprod : ℝ, 0 < Cprod ∧ ∀ V : Grassmannian K m k,
      (∏ i : Fin k,
          ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^
            degree K) ≤ Cprod * rowSpaceHeight V := by
  obtain ⟨C, hC, hbound⟩ := hFS m k
  refine ⟨C ^ degree K, pow_pos hC _, ?_⟩
  intro V
  exact rowSuccessiveMinimum_prod_norm_pow_le_of_fiekerStehle V C hk hbound

/- [derived consequence] This is the rank-one instance of the product
   inequality in Part 1 of `le:props_of_minima` (papers/katznelson.tex,
   lines 899--907).  Unlike the all-rank version immediately above, it is
   discharged from the proved first Minkowski theorem through
   `exists_fiekerStehleProductBound_rank_one`; it has no Fieker--Stehlé
   hypothesis. -/
theorem exists_rowSuccessiveMinimum_prod_norm_pow_le_rank_one
    (m : ℕ) :
    ∃ Cprod : ℝ, 0 < Cprod ∧ ∀ V : Grassmannian K m 1,
      (∏ i : Fin 1,
        ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^
          degree K) ≤ Cprod * rowSpaceHeight V := by
  obtain ⟨C, hC, hFS⟩ := exists_fiekerStehleProductBound_rank_one (K := K) m
  refine ⟨C ^ degree K, pow_pos hC _, ?_⟩
  intro V
  exact rowSuccessiveMinimum_prod_norm_pow_le_of_fiekerStehle V C (by omega) hFS

/- The first admissible set is nonempty whenever the Grassmannian rank is
   positive.  The proof uses the already formalized full-lattice Minkowski
   theorem, so the total fallback in `successiveMinimum` is not used here. -/
theorem rowSuccessiveMinimumSet_zero_nonempty
    (hk : 0 < k) :
    (successiveMinimumSet K 0 (rowZLattice V)
      (successiveMinimaAux K (rowZLattice V) 0)).Nonempty := by
  letI : Nontrivial (rowRealSpan V) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [rowRealSpan_finrank V]
    exact Nat.mul_pos hk Module.finrank_pos
  obtain ⟨w, hw, _⟩ :=
    exists_nonzero_latticeVector_norm_le_covolume_rpow (rowZLattice V)
  refine ⟨w, ?_⟩
  rw [successiveMinimumSet_zero]
  intro hw'
  apply hw
  exact Subtype.ext hw'

/- This is the first inequality in part 1 of `le:props_of_minima`, with the
   paper's exponent `1/(d k)` written as `1/(k * degree K)`. -/
theorem rowSuccessiveMinimum_first_norm_le
    (hk : 0 < k) :
    ‖((rowSuccessiveMinimum V ⟨0, hk⟩ : rowZLattice V) : rowRealSpan V)‖ ≤
      minkowskiConstant (E := rowRealSpan V) *
        (rowSpaceHeight V) ^ (1 / (k * degree K : ℝ)) := by
  letI : Nontrivial (rowRealSpan V) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [rowRealSpan_finrank V]
    exact Nat.mul_pos hk Module.finrank_pos
  have hA := rowSuccessiveMinimumSet_zero_nonempty V hk
  obtain ⟨w, hw, hwb⟩ :=
    exists_nonzero_latticeVector_norm_le_covolume_rpow (rowZLattice V)
  have hwA : w ∈ successiveMinimumSet K 0 (rowZLattice V)
      (successiveMinimaAux K (rowZLattice V) 0) := by
    rw [successiveMinimumSet_zero]
    intro hw'
    apply hw
    exact Subtype.ext hw'
  have hmin := rowSuccessiveMinimum_norm_min_of_nonempty V ⟨0, hk⟩ hA w hwA
  calc
    ‖((rowSuccessiveMinimum V ⟨0, hk⟩ : rowZLattice V) : rowRealSpan V)‖ ≤
        minkowskiConstant (E := rowRealSpan V) *
          (ZLattice.covolume (rowZLattice V)
            (volume : Measure (rowRealSpan V))) ^
            (1 / (Module.finrank ℝ (rowRealSpan V) : ℝ)) :=
      hmin.trans hwb
    _ = minkowskiConstant (E := rowRealSpan V) *
        (rowSpaceHeight V) ^ (1 / (k * degree K : ℝ)) := by
      rw [← rowSpaceHeight_eq_volume_covolume V, rowRealSpan_finrank V,
        Nat.cast_mul]

/- [derived consequence] This makes the first inequality of Part 1 of
   `le:props_of_minima` (papers/katznelson.tex, lines 899--907) uniform over
   rank-`k` row lattices.  The paper denotes the resulting fixed constant by
   `C^{hermite}`.  It follows from the already proved first Minkowski bound;
   it is not an invocation of the separate Fieker--Stehlé product theorem. -/
theorem exists_uniform_rowSuccessiveMinimum_first_norm_le
    (m k : ℕ) (hk : 0 < k) :
    ∃ Chermite : ℝ, 0 < Chermite ∧ ∀ V : Grassmannian K m k,
      ‖((rowSuccessiveMinimum V ⟨0, hk⟩ : rowZLattice V) :
        rowRealSpan V)‖ ≤
        Chermite * (rowSpaceHeight V) ^ (1 / (k * degree K : ℝ)) := by
  letI : Nonempty (Fin (k * degree K)) :=
    ⟨⟨0, Nat.mul_pos hk Module.finrank_pos⟩⟩
  letI : Nontrivial (EuclideanSpace ℝ (Fin (k * degree K))) := by
    infer_instance
  refine ⟨minkowskiConstant (E := EuclideanSpace ℝ (Fin (k * degree K))),
    minkowskiConstant_pos, ?_⟩
  intro V
  letI : Nontrivial (rowRealSpan V) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [rowRealSpan_finrank V]
    exact Nat.mul_pos hk Module.finrank_pos
  have hfirst := rowSuccessiveMinimum_first_norm_le V hk
  have hdimension : Module.finrank ℝ (rowRealSpan V) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (k * degree K))) := by
    rw [rowRealSpan_finrank V]
    simp
  have hconstant : minkowskiConstant (E := rowRealSpan V) =
      minkowskiConstant (E := EuclideanSpace ℝ (Fin (k * degree K))) :=
    minkowskiConstant_eq_of_finrank_eq (E := rowRealSpan V) hdimension
  rw [hconstant] at hfirst
  exact hfirst

end RowSuccessiveMinima

end Katznelson
