import Katznelson.Counting.MinkowskiSecond

/-!
# The Fieker--Stehlé product bound for the manuscript's minima

Fieker--Stehlé, *Short Bases of Lattices over Number Fields*, Theorem 2
(`papers/Fieker-Stehle-ShortBases-2010.pdf`, p. 3), obtains a product bound
for number-field module minima by applying Minkowski's second theorem to the
underlying integral lattice.  Its proof selects, for the `i`-th field minimum,
one of the first `i * [K : Q] + 1` real minima outside the preceding field
span.

This module formalizes that selection argument directly for the recursively
defined manuscript vectors `l_i = rowSuccessiveMinimum V i`.  It uses the
Euclidean Minkowski-II supporting theorem in `MinkowskiSecond.lean` and adds
no cited hypothesis.  Its metric is the repository's existing raw Euclidean
row realization; it does not identify that metric with the manuscript's
trace/discriminant normalization.  The required fixed-field normalization
bridge remains explicitly recorded in `notes/formalization-issues.md`.
The resulting raw-metric constant is deliberately non-sharp, as only a
constant uniform in the row lattice is used at this stage.
-/

namespace Katznelson

open MeasureTheory Set Metric Module
open scoped Classical NumberField RealInnerProductSpace

section FiekerStehle

variable {K : Type*} [Field K] [NumberField K]
  {m k : ℕ} (V : Grassmannian K m k)

/- [Lean infrastructure] These local structures make the Euclidean topology
   on the manuscript row space explicit.  They are the same induced subtype
   structures used by `RowLattice` and `SuccessiveMinima`; no new norm or
   measure is introduced here. -/
noncomputable local instance fiekerStehleAmbientMeasurableSpace :
    MeasurableSpace (RowVector K m) := borel (RowVector K m)

local instance fiekerStehleAmbientBorelSpace :
    @BorelSpace (RowVector K m) _ fiekerStehleAmbientMeasurableSpace :=
  ⟨rfl⟩

noncomputable local instance fiekerStehleMeasurableSpace :
    MeasurableSpace (rowRealSpan V) :=
  @Subtype.instMeasurableSpace (RowVector K m)
    (fun x => x ∈ rowRealSpan V) fiekerStehleAmbientMeasurableSpace

local instance fiekerStehleBorelSpace :
    BorelSpace (rowRealSpan V) :=
  @Subtype.borelSpace (RowVector K m) _ fiekerStehleAmbientMeasurableSpace
    fiekerStehleAmbientBorelSpace (fun x => x ∈ rowRealSpan V)

noncomputable local instance fiekerStehleInnerProductSpace :
    InnerProductSpace ℝ (rowRealSpan V) :=
  Submodule.innerProductSpace (rowRealSpan V)

/- [Lean infrastructure] Finite-dimensional linear algebra isolated from the
   number-field structures used below.  An independent prefix of length
   `r + 1` cannot be contained in a subspace of dimension at most `r`. -/
theorem exists_prefix_not_mem_of_finrank_le
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {n r : ℕ} (v : Fin n → E) (e : Fin (r + 1) → Fin n)
    (he : Function.Injective e) (hLI : LinearIndependent ℝ v)
    (W : Submodule ℝ E) (hW : Module.finrank ℝ W ≤ r) :
    ∃ q : Fin (r + 1), v (e q) ∉ W := by
  have hLIprefix : LinearIndependent ℝ (v ∘ e) := hLI.comp e he
  by_contra hno
  push_neg at hno
  have hspan : Submodule.span ℝ (Set.range (v ∘ e)) ≤ W := by
    apply Submodule.span_le.2
    rintro x ⟨q, rfl⟩
    exact hno q
  have hdim := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hLIprefix] at hdim
  simp only [Fintype.card_fin] at hdim
  omega

/- [Lean infrastructure] Initial-segment form of the preceding dimension
   argument, avoiding repeated coercion through a separately named prefix
   embedding in the number-field specialization. -/
theorem exists_index_le_not_mem_of_finrank_le
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {n r : ℕ} (v : Fin n → E) (hLI : LinearIndependent ℝ v)
    (hrn : r < n) (W : Submodule ℝ E) (hW : Module.finrank ℝ W ≤ r) :
    ∃ j : Fin n, j.val ≤ r ∧ v j ∉ W := by
  let e : Fin (r + 1) → Fin n := fun q =>
    ⟨q.val, q.isLt.trans_le (Nat.succ_le_iff.mpr hrn)⟩
  have he : Function.Injective e := by
    intro q q' h
    apply Fin.ext
    simpa only [e] using congrArg Fin.val h
  obtain ⟨q, hq⟩ :=
    exists_prefix_not_mem_of_finrank_le v e he hLI W hW
  exact ⟨e q, Nat.le_of_lt_succ q.isLt, hq⟩

/- [Lean infrastructure] The purely finite-product bookkeeping in the
   Fieker--Stehlé block argument.  Each block repeats its first (hence
   smallest) entry `d` times and is then compared termwise with the full
   monotone sequence. -/
theorem fin_prod_block_pow_le_prod
    {k d : ℕ} (hd : 0 < d) (x : Fin k → ℝ) (a : Fin (k * d) → ℝ)
    (hx_nonneg : ∀ i, 0 ≤ x i) (ha_nonneg : ∀ j, 0 ≤ a j)
    (hblock : ∀ i, x i ≤ a ⟨i.val * d,
      Nat.mul_lt_mul_of_pos_right i.isLt hd⟩)
    (hmono : ∀ i j, i.val ≤ j.val → a i ≤ a j) :
    (∏ i : Fin k, x i ^ d) ≤ ∏ j : Fin (k * d), a j := by
  let b : Fin k → Fin (k * d) := fun i =>
    ⟨i.val * d, Nat.mul_lt_mul_of_pos_right i.isLt hd⟩
  have hblocks : (∏ i : Fin k, x i ^ d) ≤
      ∏ i : Fin k, a (b i) ^ d := by
    apply Finset.prod_le_prod
    · intro i _
      exact pow_nonneg (hx_nonneg i) _
    · intro i _
      exact pow_le_pow_left₀ (hx_nonneg i) (hblock i) _
  have hrepeat : (∏ i : Fin k, a (b i) ^ d) =
      ∏ p : Fin k × Fin d, a (b p.1) := by
    calc
      (∏ i : Fin k, a (b i) ^ d) =
          ∏ i : Fin k, ∏ _j : Fin d, a (b i) := by simp
      _ = ∏ p : Fin k × Fin d, a (b p.1) :=
        (Fintype.prod_prod_type
          (fun p : Fin k × Fin d => a (b p.1))).symm
  have hreindex : (∏ p : Fin k × Fin d, a (b p.1)) =
      ∏ j : Fin (k * d), a (b (finProdFinEquiv.symm j).1) := by
    refine Fintype.prod_equiv finProdFinEquiv
      (fun p => a (b p.1))
      (fun j => a (b (finProdFinEquiv.symm j).1)) ?_
    intro p
    simp
  have hpoint (j : Fin (k * d)) :
      a (b (finProdFinEquiv.symm j).1) ≤ a j := by
    apply hmono
    calc
      (b (finProdFinEquiv.symm j).1).val ≤
          (finProdFinEquiv (finProdFinEquiv.symm j)).val := by
        dsimp only [b]
        rw [show (finProdFinEquiv (finProdFinEquiv.symm j)).val =
          (finProdFinEquiv.symm j).2.val +
            d * (finProdFinEquiv.symm j).1.val by rfl]
        rw [Nat.mul_comm (finProdFinEquiv.symm j).1.val d]
        omega
      _ = j.val := congrArg Fin.val (finProdFinEquiv.apply_symm_apply j)
  have hreal : (∏ j : Fin (k * d),
      a (b (finProdFinEquiv.symm j).1)) ≤ ∏ j : Fin (k * d), a j := by
    apply Finset.prod_le_prod
    · intro j _
      exact ha_nonneg _
    · intro j _
      exact hpoint j
  calc
    (∏ i : Fin k, x i ^ d) ≤ ∏ i : Fin k, a (b i) ^ d := hblocks
    _ = ∏ p : Fin k × Fin d, a (b p.1) := hrepeat
    _ = ∏ j : Fin (k * d), a (b (finProdFinEquiv.symm j).1) := hreindex
    _ ≤ ∏ j : Fin (k * d), a j := hreal

/- [Lean infrastructure] The upper bound carried by a `Fin` index is not
   part of the recursive minimum: `successiveMinimum` depends only on the
   index value.  This bridge avoids transporting the entire recursive
   construction when the exact row-space dimension is rewritten. -/
theorem successiveMinimum_eq_of_val_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [LinearOrder E]
    {S : Type*} [Semiring S] [Module S E]
    {p q : ℕ} (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (i : Fin p) (j : Fin q)
    (hij : i.val = j.val) :
    successiveMinimum S L i = successiveMinimum S L j := by
  change successiveMinimaAux S L (i.val + 1)
      ⟨i.val, Nat.lt_succ_self i.val⟩ =
    successiveMinimaAux S L (j.val + 1)
      ⟨j.val, Nat.lt_succ_self j.val⟩
  rw [hij]

/- [Lean infrastructure] Canonical index of the last real minimum in the
   `i`-th degree-sized block.  Naming it avoids repeated dependent casts
   between `Fin (k * degree K)` and the definitionally equal real finrank. -/
noncomputable def rowRealMinimumBlockIndex (i : Fin k) :
    Fin (Module.finrank ℝ (rowRealSpan V)) :=
  ⟨i.val * degree K, by
    simpa only [rowRealSpan_finrank V] using
      Nat.mul_lt_mul_of_pos_right i.isLt
        (show 0 < degree K from Module.finrank_pos)⟩

/- [derived consequence] This is the block-selection step in the proof of
   Fieker--Stehlé Theorem 2 (p. 3): among the first
   `i * degree K + 1` real successive minima, one lies outside the preceding
   `K`-span.  The contradiction uses the proved bound on the real dimension of
   `rowKRealCombinationMap`; its conclusion is stated in the manuscript's
   recursive `l_i` notation. -/
set_option maxHeartbeats 100000 in
theorem rowSuccessiveMinimum_norm_le_realMinimum_block (i : Fin k) :
    ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ≤
      ‖((successiveMinimum ℝ (rowZLattice V)
        (rowRealMinimumBlockIndex V i) :
          rowZLattice V) : rowRealSpan V)‖ := by
  let n : ℕ := k * degree K
  let L : Submodule ℤ (rowRealSpan V) := rowZLattice V
  let v : Fin n → rowRealSpan V := fun j =>
    ((successiveMinimum ℝ L j : L) : rowRealSpan V)
  let r : ℕ := i.val * degree K
  have hrn : r < n := by
    dsimp only [r, n]
    exact Nat.mul_lt_mul_of_pos_right i.isLt
      (show 0 < degree K from Module.finrank_pos)
  have hfull : Module.finrank ℝ
      (Submodule.span ℝ (L : Set (rowRealSpan V))) = n := by
    dsimp [L, n]
    rw [IsZLattice.span_top]
    simp [rowRealSpan_finrank V]
  have hLI : LinearIndependent ℝ v := by
    simpa only [v] using
      (successiveMinimum_linearIndependent_of_finrank n L hfull)
  have hnotall : ∃ j : Fin n, j.val ≤ r ∧
      v j ∉ LinearMap.range
        (rowKRealCombinationMap V
          (successiveMinimaAux K (rowZLattice V) i.val)) := by
    apply exists_index_le_not_mem_of_finrank_le v hLI hrn
    simpa only [r] using
      (rowKRealCombinationMap_range_finrank_le V
        (successiveMinimaAux K (rowZLattice V) i.val))
  obtain ⟨j, hj, hjrange⟩ := hnotall
  have hjout : v j ∉
      previousKSpan K (rowZLattice V) i.val
        (successiveMinimaAux K (rowZLattice V) i.val) := by
    intro hmem
    apply hjrange
    exact mem_range_rowKRealCombinationMap_of_mem_previous V
      (successiveMinimaAux K (rowZLattice V) i.val) hmem
  have hbound : ‖v j‖ ≤ ‖v ⟨r, by
        dsimp [r, n]
        exact Nat.mul_lt_mul_of_pos_right i.isLt
          (show 0 < degree K from Module.finrank_pos)⟩‖ := by
    simpa only [v] using
      (successiveMinimum_norm_le_of_index_le_of_finrank n L hfull j
        ⟨r, by
          dsimp [r, n]
          exact Nat.mul_lt_mul_of_pos_right i.isLt
            (show 0 < degree K from Module.finrank_pos)⟩ hj)
  calc
    ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ≤
        ‖v j‖ := by
      simpa only [v, L] using
        (rowSuccessiveMinimum_norm_min V i
          (successiveMinimum ℝ L j) hjout)
    _ ≤ ‖v ⟨r, by
      dsimp [r, n]
      exact Nat.mul_lt_mul_of_pos_right i.isLt
        (show 0 < degree K from Module.finrank_pos)⟩‖ := hbound
    _ = ‖((successiveMinimum ℝ (rowZLattice V)
      (rowRealMinimumBlockIndex V i) :
        rowZLattice V) : rowRealSpan V)‖ := by
      congr 3

/- [derived consequence] Repeating the preceding block comparison `degree K`
   times and reindexing `Fin k × Fin (degree K)` by `finProdFinEquiv` bounds
   the manuscript product by the complete real-successive-minima product.  This
   is the displayed product comparison in the proof of Fieker--Stehlé Theorem
   2, expressed for the manuscript's recursively chosen `l_i`. -/
set_option maxHeartbeats 100000 in
theorem rowSuccessiveMinimum_product_le_euclidean_minima :
    (∏ i : Fin k,
      ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^
        degree K) ≤
      ∏ j : Fin (Module.finrank ℝ (rowRealSpan V)),
        ‖((successiveMinimum ℝ (rowZLattice V) j : rowZLattice V) :
          rowRealSpan V)‖ := by
  rw [rowRealSpan_finrank V]
  let x : Fin k → ℝ := fun i =>
    ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖
  let a : Fin (k * degree K) → ℝ := fun j =>
    ‖((successiveMinimum ℝ (rowZLattice V) j : rowZLattice V) :
      rowRealSpan V)‖
  have hfull : Module.finrank ℝ
      (Submodule.span ℝ
        (rowZLattice V : Set (rowRealSpan V))) = k * degree K := by
    rw [IsZLattice.span_top]
    simp [rowRealSpan_finrank V]
  have hblock : ∀ i, x i ≤ a ⟨i.val * degree K,
      Nat.mul_lt_mul_of_pos_right i.isLt
        (show 0 < degree K from Module.finrank_pos)⟩ := by
    intro i
    dsimp only [x, a]
    have hsame :
        successiveMinimum ℝ (rowZLattice V)
            ⟨i.val * degree K,
              Nat.mul_lt_mul_of_pos_right i.isLt
                (show 0 < degree K from Module.finrank_pos)⟩ =
          successiveMinimum ℝ (rowZLattice V)
            (rowRealMinimumBlockIndex V i) :=
      successiveMinimum_eq_of_val_eq (rowZLattice V) _ _ rfl
    rw [hsame]
    exact rowSuccessiveMinimum_norm_le_realMinimum_block V i
  have hmono : ∀ p q : Fin (k * degree K),
      p.val ≤ q.val → a p ≤ a q := by
    intro p q hpq
    dsimp only [a]
    exact successiveMinimum_norm_le_of_index_le_of_finrank
      (k * degree K) (rowZLattice V) hfull p q hpq
  exact fin_prod_block_pow_le_prod
    (k := k) (d := degree K)
    (show 0 < degree K from Module.finrank_pos) x a
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hblock hmono

/- [derived consequence] Row-space specialization of the proved Euclidean
   Minkowski-II theorem in `MinkowskiSecond.lean`.  The measure is written
   explicitly so that the induced-volume instance is not hidden by an
   `autoParam` while this result is transported to `rowSpaceHeight`. -/
set_option maxHeartbeats 1000000 in
theorem rowEuclideanSuccessiveMinimum_product_le_covolume (hk : 0 < k) :
    (∏ j : Fin (Module.finrank ℝ (rowRealSpan V)),
      ‖((successiveMinimum ℝ (rowZLattice V) j : rowZLattice V) :
        rowRealSpan V)‖) ≤
      ((Module.finrank ℝ (rowRealSpan V) : ℝ) *
          minkowskiConstant (E := rowRealSpan V)) ^
        Module.finrank ℝ (rowRealSpan V) *
        ZLattice.covolume (rowZLattice V)
          (volume : Measure (rowRealSpan V)) := by
  letI : Nontrivial (rowRealSpan V) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [rowRealSpan_finrank V]
    exact Nat.mul_pos hk Module.finrank_pos
  exact euclidean_successiveMinimum_product_le_covolume
    (E := rowRealSpan V) (rowZLattice V)

/- [Lean infrastructure] Exact normalization of the Euclidean supporting
   estimate to one constant depending only on `k` and `K`.  The covolume
   equality is the proved internal raw-metric identity; no manuscript metric
   is silently identified here. -/
set_option maxHeartbeats 100000 in
theorem rowEuclideanMinkowski_covolume_eq_height (hk : 0 < k) :
    ((Module.finrank ℝ (rowRealSpan V) : ℝ) *
        minkowskiConstant (E := rowRealSpan V)) ^
        Module.finrank ℝ (rowRealSpan V) *
        ZLattice.covolume (rowZLattice V)
          (volume : Measure (rowRealSpan V)) =
      ((k * degree K : ℝ) *
          minkowskiConstant (E := EuclideanSpace ℝ (Fin (k * degree K)))) ^
        (k * degree K) * rowSpaceHeight V := by
  letI : Nonempty (Fin (k * degree K)) :=
    ⟨⟨0, Nat.mul_pos hk (show 0 < degree K from Module.finrank_pos)⟩⟩
  letI : Nontrivial (EuclideanSpace ℝ (Fin (k * degree K))) := by
    infer_instance
  letI : Nontrivial (rowRealSpan V) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [rowRealSpan_finrank V]
    exact Nat.mul_pos hk Module.finrank_pos
  have hdimension : Module.finrank ℝ (rowRealSpan V) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (k * degree K))) := by
    rw [rowRealSpan_finrank V]
    simp
  have hconstant : minkowskiConstant (E := rowRealSpan V) =
      minkowskiConstant (E := EuclideanSpace ℝ (Fin (k * degree K))) :=
    minkowskiConstant_eq_of_finrank_eq (E := rowRealSpan V) hdimension
  rw [rowRealSpan_finrank V, hconstant,
    ← rowSpaceHeight_eq_volume_covolume V]
  norm_num [Nat.cast_mul]

/- [derived consequence] Combining the preceding Fieker--Stehlé selection
   argument with the locally proved Euclidean Minkowski-II estimate yields the
   uniform-in-lattice raw-Euclidean product estimate corresponding to part 1
   of `le:props_of_minima` (papers/katznelson.tex, lines 924--934).  This is a
   proved supporting derivation of the cited input, not an additional
   assumption; the separately recorded metric-normalization bridge is not
   claimed here. -/
set_option maxHeartbeats 100000 in
theorem rowSuccessiveMinimum_product_le_height_of_euclideanMinkowskiSecond
    (hk : 0 < k) :
    (∏ i : Fin k,
      ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^
        degree K) ≤
      ((k * degree K : ℝ) *
          minkowskiConstant (E := EuclideanSpace ℝ (Fin (k * degree K)))) ^
        (k * degree K) * rowSpaceHeight V := by
  calc
    (∏ i : Fin k,
      ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^
        degree K) ≤
        ∏ j : Fin (Module.finrank ℝ (rowRealSpan V)),
          ‖((successiveMinimum ℝ (rowZLattice V) j : rowZLattice V) :
            rowRealSpan V)‖ :=
      rowSuccessiveMinimum_product_le_euclidean_minima V
    _ ≤ ((Module.finrank ℝ (rowRealSpan V) : ℝ) *
          minkowskiConstant (E := rowRealSpan V)) ^
          Module.finrank ℝ (rowRealSpan V) *
          ZLattice.covolume (rowZLattice V)
            (volume : Measure (rowRealSpan V)) :=
      rowEuclideanSuccessiveMinimum_product_le_covolume V hk
    _ = ((k * degree K : ℝ) *
          minkowskiConstant (E := EuclideanSpace ℝ (Fin (k * degree K)))) ^
          (k * degree K) * rowSpaceHeight V :=
      rowEuclideanMinkowski_covolume_eq_height V hk

/- [derived consequence] This packages the preceding proved raw-Euclidean
   bound with one positive constant independent of the rank-`k` row lattice.
   It is the internal `C^{okhadamard}`-style interface used by the later
   radius-sum estimates; the paper-metric bridge remains separately tracked. -/
theorem exists_rowSuccessiveMinimum_product_le_height_of_euclideanMinkowskiSecond
    (hk : 0 < k) :
    ∃ Cprod : ℝ, 0 < Cprod ∧ ∀ W : Grassmannian K m k,
      (∏ i : Fin k,
        ‖((rowSuccessiveMinimum W i : rowZLattice W) : rowRealSpan W)‖ ^
          degree K) ≤ Cprod * rowSpaceHeight W := by
  letI : Nonempty (Fin (k * degree K)) :=
    ⟨⟨0, Nat.mul_pos hk (show 0 < degree K from Module.finrank_pos)⟩⟩
  letI : Nontrivial (EuclideanSpace ℝ (Fin (k * degree K))) := by
    infer_instance
  let Cprod : ℝ := ((k * degree K : ℝ) *
    minkowskiConstant (E := EuclideanSpace ℝ (Fin (k * degree K)))) ^
      (k * degree K)
  refine ⟨Cprod, ?_, ?_⟩
  · dsimp [Cprod]
    apply pow_pos
    apply mul_pos
    · exact_mod_cast Nat.mul_pos hk Module.finrank_pos
    · exact minkowskiConstant_pos
  · intro W
    exact rowSuccessiveMinimum_product_le_height_of_euclideanMinkowskiSecond W hk

end FiekerStehle

end Katznelson
