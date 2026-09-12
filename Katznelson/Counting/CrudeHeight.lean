import Katznelson.Counting.SuccessiveMinima
import Katznelson.Counting.Echelon
import Mathlib.Analysis.MeanInequalities

/-!
# Crude height bounds

This module formalizes the selected-row/Hadamard argument in the proof of
`le:crude_early` of the manuscript.  It deliberately retains the manuscript's
height as the covolume of the row lattice.
-/

namespace Katznelson

open MeasureTheory Set Metric Module
open scoped Classical NumberField RealInnerProductSpace

section Covolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/- [Lean infrastructure] A real basis contained in a full lattice generates a
sub-lattice.  Combining the relative-covolume formula with the manuscript's
Hadamard bound gives the form needed for the selected rows in
`le:crude_early` (lines 1091--1120). -/
theorem ZLattice.covolume_le_prod_norm_of_real_basis_mem
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (hb : ∀ i, b i ∈ L) :
    ZLattice.covolume L ≤ ∏ i, ‖b i‖ := by
  let Lb : Submodule ℤ E := Submodule.span ℤ (Set.range b)
  letI : DiscreteTopology Lb := inferInstance
  letI : IsZLattice ℝ Lb := inferInstance
  have hLb : Lb ≤ L := by
    change Submodule.span ℤ (Set.range b) ≤ L
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact hb i
  let bZ : Basis (Fin (Module.finrank ℝ E)) ℤ Lb := b.restrictScalars ℤ
  have hratio : ZLattice.covolume Lb / ZLattice.covolume L =
      (Lb.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := by
    exact ZLattice.covolume_div_covolume_eq_relIndex' Lb L hLb
  have hratio_pos : 0 < ZLattice.covolume Lb / ZLattice.covolume L := by
    exact div_pos (ZLattice.covolume_pos Lb volume) (ZLattice.covolume_pos L volume)
  have hindex_pos : 0 < Lb.toAddSubgroup.relIndex L.toAddSubgroup := by
    exact_mod_cast (hratio ▸ hratio_pos)
  have hindex_one : 1 ≤ Lb.toAddSubgroup.relIndex L.toAddSubgroup :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hindex_pos)
  have hratio_one : 1 ≤ ZLattice.covolume Lb / ZLattice.covolume L := by
    rw [hratio]
    exact_mod_cast hindex_one
  have hL_le_Lb : ZLattice.covolume L ≤ ZLattice.covolume Lb := by
    have hpos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
    rw [le_div_iff₀ hpos] at hratio_one
    simpa using hratio_one
  have hhadamard : 1 ≤ hadamardRatio Lb bZ := one_le_hadamardRatio Lb bZ
  have hLb_pos : 0 < ZLattice.covolume Lb := ZLattice.covolume_pos Lb volume
  have hLb_le : ZLattice.covolume Lb ≤ ∏ i, ‖bZ i‖ := by
    change 1 ≤ (∏ i, ‖(bZ i : Lb)‖) / ZLattice.covolume Lb at hhadamard
    rw [le_div_iff₀ hLb_pos] at hhadamard
    simpa using hhadamard
  calc
    ZLattice.covolume L ≤ ZLattice.covolume Lb := hL_le_Lb
    _ ≤ ∏ i, ‖bZ i‖ := hLb_le
    _ = ∏ i, ‖b i‖ := by
      apply Finset.prod_congr rfl
      intro i hi
      change ‖((bZ i : Lb) : E)‖ = ‖b i‖
      dsimp only [bZ]
      exact congrArg norm (Module.Basis.restrictScalars_apply ℤ b i)

/- [Lean infrastructure] Reindexing the preceding finite-dimensional
   covolume bound preserves a paper-facing basis index such as the pairs
   `(i,j)` in `w_ij`; it does not alter the lattice or its covolume. -/
theorem ZLattice.covolume_le_prod_norm_of_fintype_real_basis_mem
    {ι : Type*} [Fintype ι]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℝ E)
    (hb : ∀ i, b i ∈ L) :
    ZLattice.covolume L ≤ ∏ i, ‖b i‖ := by
  let e : Fin (Module.finrank ℝ E) ≃ ι :=
    Fintype.equivOfCardEq (by simpa using Module.finrank_eq_card_basis b)
  have hb' : ∀ i, b.reindex e.symm i ∈ L := by
    intro i
    simpa using hb (e i)
  have hbound := ZLattice.covolume_le_prod_norm_of_real_basis_mem L
    (b.reindex e.symm) hb'
  calc
    ZLattice.covolume L ≤ ∏ i, ‖b.reindex e.symm i‖ := hbound
    _ = ∏ i, ‖b i‖ := by
      simpa using (Equiv.prod_comp e (fun i => ‖b i‖))

end Covolume

section SelectedRows

variable {K : Type*} [Field K] [NumberField K]

/- [derived consequence, paper proof of `le:crude_early`, lines 1101--1107]
   The `k` selected independent rows span the same `K`-space as the full
   row lattice.  This is the algebraic content of the manuscript's phrase
   "a full-rank `K`-basis of `Λ_D ⊗ ℚ`". -/
theorem rowIndependent_K_span_eq_rowZLattice_K_span
    {m k : ℕ} (V : Grassmannian K m k)
    (v : Fin k → rowZLattice V)
    (hv : LinearIndependent K (fun i => (v i : rowRealSpan V))) :
    Submodule.span K (Set.range (fun i => (v i : rowRealSpan V))) =
      Submodule.span K (rowZLattice V : Set (rowRealSpan V)) := by
  let S : Submodule K (rowRealSpan V) :=
    Submodule.span K (Set.range (fun i => (v i : rowRealSpan V)))
  let R : Submodule K (rowRealSpan V) :=
    Submodule.span K (rowZLattice V : Set (rowRealSpan V))
  have hSR : S ≤ R := by
    change Submodule.span K (Set.range (fun i => (v i : rowRealSpan V))) ≤
      Submodule.span K (rowZLattice V : Set (rowRealSpan V))
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span (v i).property
  have hfinS : Module.finrank K S = k := by
    change Module.finrank K
      (Submodule.span K (Set.range (fun i => (v i : rowRealSpan V)))) = k
    rw [finrank_span_eq_card hv]
    simp
  have hfinR : Module.finrank K R = k := by
    exact rowZLattice_K_span_finrank V
  letI : FiniteDimensional K R := rowZLattice_K_span_finiteDimensional V
  exact Submodule.eq_of_le_of_finrank_eq hSR (hfinS.trans hfinR.symm)

/- [derived consequence, paper proof of `le:crude_early`, lines 1104--1107]
   Scalar extension of those selected `K`-basis vectors is the full real row
   span.  This is the bridge needed to make their integral-basis multiples a
   real basis. -/
theorem rowIndependent_KRealSpan_eq_top
    {m k : ℕ} (V : Grassmannian K m k)
    (v : Fin k → rowZLattice V)
    (hv : LinearIndependent K (fun i => (v i : rowRealSpan V))) :
    Submodule.span K_ℝ[K] (Set.range (fun i => (v i : rowRealSpan V))) = ⊤ := by
  let S : Submodule K (rowRealSpan V) :=
    Submodule.span K (Set.range (fun i => (v i : rowRealSpan V)))
  let SR : Submodule K_ℝ[K] (rowRealSpan V) :=
    Submodule.span K_ℝ[K] (Set.range (fun i => (v i : rowRealSpan V)))
  have hKS : S = Submodule.span K (rowZLattice V : Set (rowRealSpan V)) := by
    exact rowIndependent_K_span_eq_rowZLattice_K_span V v hv
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

/- [derived consequence, paper `le:basis_of_OK`, lines 679--700 and proof
   of `le:crude_early`, lines 1104--1107] The vectors `w_ij = u_j v_i`, with
   `u_j` the fixed integral basis, form the real basis underlying the
   manuscript's `ℤ`-basis of `𝓞_K v₁ ⊕ ⋯ ⊕ 𝓞_K v_k`. -/
noncomputable def rowIndependentRealBasis
    {m k : ℕ} (V : Grassmannian K m k)
    (v : Fin k → rowZLattice V)
    (hv : LinearIndependent K (fun i => (v i : rowRealSpan V))) :
    Basis (Σ _ : Fin k, IntegralBasisIndex K) ℝ (rowRealSpan V) := by
  letI : Fintype (IntegralBasisIndex K) := Fintype.ofFinite _
  let f := rowKRealCombinationMap V v
  have hspan : Submodule.span K_ℝ[K] (Set.range (fun i =>
      (v i : rowRealSpan V))) = ⊤ :=
    rowIndependent_KRealSpan_eq_top V v hv
  have hrange : LinearMap.range f = ⊤ :=
    rowKRealCombinationMap_range_eq_top_of_KRealSpan V v hspan
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

/- [derived consequence, paper `le:basis_of_OK`, lines 679--700] This is the
   displayed formula `w_ij = u_j v_i` for the preceding basis. -/
theorem rowIndependentRealBasis_apply
    {m k : ℕ} (V : Grassmannian K m k)
    (v : Fin k → rowZLattice V)
    (hv : LinearIndependent K (fun i => (v i : rowRealSpan V)))
    (i : Fin k) (j : IntegralBasisIndex K) :
    rowIndependentRealBasis V v hv ⟨i, j⟩ =
      numberEmbedding K (NumberField.integralBasis K j) •
        (v i : rowRealSpan V) := by
  classical
  simp [rowIndependentRealBasis, numberFieldEuclideanBasis,
    rowKRealCombinationMap, numberEmbedding,
    NumberField.mixedEmbedding.latticeBasis_apply]

/- [derived consequence, paper proof of `le:crude_early`, lines 1104--1109]
   Each `w_ij` belongs to the original row lattice, so the lattice generated
   by the selected free `𝓞_K`-module is a sublattice of `Λ_D`. -/
theorem rowIndependentRealBasis_mem_rowZLattice
    {m k : ℕ} (V : Grassmannian K m k)
    (v : Fin k → rowZLattice V)
    (hv : LinearIndependent K (fun i => (v i : rowRealSpan V)))
    (i : Fin k) (j : IntegralBasisIndex K) :
    rowIndependentRealBasis V v hv ⟨i, j⟩ ∈ rowZLattice V := by
  classical
  rw [rowIndependentRealBasis_apply]
  rw [NumberField.integralBasis_apply]
  change numberEmbedding K
      (algebraMap (𝓞 K) K (NumberField.RingOfIntegers.basis K j)) •
      (v i : rowRealSpan V) ∈ rowZLattice V
  change numberEmbedding K
      (algebraMap (𝓞 K) K (NumberField.RingOfIntegers.basis K j)) •
      ((v i : rowRealSpan V) : RowVector K m) ∈ embeddedIntegralRowModule V
  exact embeddedIntegralRowModule_smul_integral V
    (NumberField.RingOfIntegers.basis K j)
    (v i).property

/- [paper, proof of `le:crude_early`, lines 1103--1110] A selected row of
   the full-rank witness matrix has norm at most its Frobenius norm.  This is
   the first inequality in the manuscript's displayed square-norm estimate. -/
theorem rowMatrixZLattice_selectedRow_norm_le
    {m k n : ℕ} (V : Grassmannian K m k)
    (A : rowMatrixZLattice V n) (e : Fin k → Fin n) (i : Fin k) :
    ‖((rowMatrixZLatticeEquiv V A (e i) : rowZLattice V) : rowRealSpan V)‖ ≤
      ‖(A : rowMatrixRealSpan V n)‖ := by
  rw [rowMatrixZLatticeEquiv_norm_coe]
  calc
    ‖rowVectorOfFun (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K])) (e i))‖ ≤
        ‖((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))‖ :=
      norm_rowVectorOfFun_le_frobenius _ _
    _ = ‖(A : rowMatrixRealSpan V n)‖ := rfl

/- [paper, proof of `le:crude_early`, lines 1110--1112] The squared norms
   of pairwise distinct selected rows are bounded by the squared Frobenius
   norm of the witness matrix.  This is the first inequality in the displayed
   estimate at line 1112, before it is combined with `w_ij = u_j v_i`. -/
set_option maxHeartbeats 1000000 in
theorem rowMatrixZLattice_selectedRows_sq_sum_le
    {m k n : ℕ} (V : Grassmannian K m k)
    (A : rowMatrixZLattice V n) (e : Fin k → Fin n)
    (he : Function.Injective e) :
    (∑ i : Fin k,
      ‖((rowMatrixZLatticeEquiv V A (e i) : rowZLattice V) : rowRealSpan V)‖ ^ 2) ≤
      ‖(A : rowMatrixRealSpan V n)‖ ^ 2 := by
  classical
  let X : PiLp 2 (fun _ : Fin n => rowRealSpan V) :=
    rowMatrixRealSpanLpEquiv V (A : rowMatrixRealSpan V n)
  have hrow (r : Fin n) :
      ‖X r‖ = ‖((rowMatrixZLatticeEquiv V A r : rowZLattice V) : rowRealSpan V)‖ := by
    change ‖rowVectorOfFun
      (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K])) r)‖ = _
    exact (rowMatrixZLatticeEquiv_norm_coe V A r).symm
  let e' : Fin k ↪ Fin n := ⟨e, he⟩
  let s : Finset (Fin n) := Finset.univ.map e'
  have hs : s ⊆ Finset.univ := by
    intro r hr
    simp
  have hsubset : (∑ r ∈ s, ‖X r‖ ^ 2) ≤ ∑ r : Fin n, ‖X r‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun r _ _ => sq_nonneg (‖X r‖))
  have hmap : (∑ r ∈ s, ‖X r‖ ^ 2) = ∑ i : Fin k, ‖X (e i)‖ ^ 2 := by
    change (∑ r ∈ Finset.univ.map e', ‖X r‖ ^ 2) = _
    rw [Finset.sum_map]
    change (∑ i : Fin k, ‖X (e i)‖ ^ 2) = _
    rfl
  have hnorm : (∑ r : Fin n, ‖X r‖ ^ 2) = ‖(A : rowMatrixRealSpan V n)‖ ^ 2 := by
    rw [← PiLp.norm_sq_eq_of_L2]
    exact congrArg (fun z : ℝ => z ^ 2)
      (rowMatrixRealSpanLpEquiv_norm V (A : rowMatrixRealSpan V n))
  calc
    (∑ i : Fin k,
      ‖((rowMatrixZLatticeEquiv V A (e i) : rowZLattice V) : rowRealSpan V)‖ ^ 2) =
        ∑ i : Fin k, ‖X (e i)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hrow]
    _ = ∑ r ∈ s, ‖X r‖ ^ 2 := hmap.symm
    _ ≤ ∑ r : Fin n, ‖X r‖ ^ 2 := hsubset
    _ = ‖(A : rowMatrixRealSpan V n)‖ ^ 2 := hnorm

/- [derived consequence, paper `le:basis_of_OK`, lines 679--700] For a fixed
   integral-basis element, this is a finite operator bound for multiplication
   by its inverse image in `K_ℝ`.  It supplies the lower half of the displayed
   `C^okl ‖v_i‖ ≤ ‖u_j v_i‖` comparison. -/
noncomputable def rowIntegralBasisInverseActionBound
    {m : ℕ} (j : IntegralBasisIndex K) : ℝ :=
  Classical.choose (exists_rowKRealScalar_bound (m := m)
    (numberEmbedding K ((NumberField.integralBasis K j)⁻¹)))

theorem rowIntegralBasisInverseActionBound_pos
    {m : ℕ} (j : IntegralBasisIndex K) :
    0 < rowIntegralBasisInverseActionBound (K := K) (m := m) j :=
  (Classical.choose_spec (exists_rowKRealScalar_bound (m := m)
    (numberEmbedding K ((NumberField.integralBasis K j)⁻¹)))).1

theorem rowIntegralBasisInverseActionBound_apply
    {m : ℕ} (j : IntegralBasisIndex K) (x : RowVector K m) :
    ‖numberEmbedding K ((NumberField.integralBasis K j)⁻¹) • x‖ ≤
      rowIntegralBasisInverseActionBound (K := K) (m := m) j * ‖x‖ :=
  (Classical.choose_spec (exists_rowKRealScalar_bound (m := m)
    (numberEmbedding K ((NumberField.integralBasis K j)⁻¹)))).2 x

/- [derived consequence, paper `le:basis_of_OK`, lines 679--700] A nonzero
   integral-basis vector acts invertibly on every row vector.  We retain the
   manuscript's `u_j v_i` notation through `numberFieldEuclideanBasis`. -/
theorem rowIntegralBasis_inverse_smul_smul
    {m : ℕ} (j : IntegralBasisIndex K) (x : RowVector K m) :
    numberEmbedding K ((NumberField.integralBasis K j)⁻¹) •
        (numberFieldEuclideanBasis (K := K) j • x) = x := by
  have hj : NumberField.integralBasis K j ≠ 0 :=
    Module.Basis.ne_zero (NumberField.integralBasis K) j
  have hmul : numberEmbedding K ((NumberField.integralBasis K j)⁻¹) *
      numberEmbedding K (NumberField.integralBasis K j) = 1 := by
    change numberEmbeddingRingHom K ((NumberField.integralBasis K j)⁻¹) *
      numberEmbeddingRingHom K (NumberField.integralBasis K j) = 1
    rw [← map_mul, inv_mul_cancel₀ hj, map_one]
  rw [numberFieldEuclideanBasis_apply, ← mul_smul, hmul, one_smul]

/- [derived consequence, paper `le:basis_of_OK`, lines 679--700] The finite
   family of inverse-action bounds is replaced by one positive constant.  It
   is the Lean representative of the paper's fixed `C^okl`. -/
noncomputable def rowIntegralBasisLowerDenominator {m : ℕ} : ℝ := by
  letI : Fintype (IntegralBasisIndex K) := Fintype.ofFinite _
  exact 1 + ∑ j : IntegralBasisIndex K,
    rowIntegralBasisInverseActionBound (K := K) (m := m) j

noncomputable def rowIntegralBasisLowerConstant {m : ℕ} : ℝ :=
  (rowIntegralBasisLowerDenominator (K := K) (m := m))⁻¹

theorem rowIntegralBasisLowerDenominator_pos {m : ℕ} :
    0 < rowIntegralBasisLowerDenominator (K := K) (m := m) := by
  classical
  letI : Fintype (IntegralBasisIndex K) := Fintype.ofFinite _
  rw [rowIntegralBasisLowerDenominator]
  have hsum : 0 ≤ ∑ j : IntegralBasisIndex K,
      rowIntegralBasisInverseActionBound (K := K) (m := m) j :=
    Finset.sum_nonneg fun j _ =>
      (rowIntegralBasisInverseActionBound_pos (K := K) (m := m) j).le
  linarith

theorem rowIntegralBasisLowerConstant_pos {m : ℕ} :
    0 < rowIntegralBasisLowerConstant (K := K) (m := m) := by
  rw [rowIntegralBasisLowerConstant]
  exact inv_pos.mpr (rowIntegralBasisLowerDenominator_pos (K := K) (m := m))

/- [derived consequence, paper `le:basis_of_OK`, lines 679--700] This is the
   uniform lower comparison `C^okl ‖x‖ ≤ ‖u_j x‖` for the fixed integral
   basis.  It is stated in the manuscript's multiplication notation. -/
theorem rowIntegralBasisLowerConstant_apply
    {m : ℕ} (j : IntegralBasisIndex K) (x : RowVector K m) :
    rowIntegralBasisLowerConstant (K := K) (m := m) * ‖x‖ ≤
      ‖numberFieldEuclideanBasis (K := K) j • x‖ := by
  classical
  letI : Fintype (IntegralBasisIndex K) := Fintype.ofFinite _
  have hinvbound := rowIntegralBasisInverseActionBound_apply (K := K)
    (m := m) j (numberFieldEuclideanBasis (K := K) j • x)
  rw [rowIntegralBasis_inverse_smul_smul] at hinvbound
  have hsingle : rowIntegralBasisInverseActionBound (K := K) (m := m) j ≤
      ∑ j' : IntegralBasisIndex K,
        rowIntegralBasisInverseActionBound (K := K) (m := m) j' := by
    exact Finset.single_le_sum
      (fun j' _ => (rowIntegralBasisInverseActionBound_pos (K := K) (m := m) j').le)
      (Finset.mem_univ j)
  have hbound : rowIntegralBasisInverseActionBound (K := K) (m := m) j ≤
      rowIntegralBasisLowerDenominator (K := K) (m := m) := by
    rw [rowIntegralBasisLowerDenominator]
    linarith
  have hnorm : ‖x‖ ≤ rowIntegralBasisLowerDenominator (K := K) (m := m) *
      ‖numberFieldEuclideanBasis (K := K) j • x‖ :=
    hinvbound.trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))
  calc
    rowIntegralBasisLowerConstant (K := K) (m := m) * ‖x‖ =
        ‖x‖ / rowIntegralBasisLowerDenominator (K := K) (m := m) := by
      simp [rowIntegralBasisLowerConstant, div_eq_mul_inv, mul_comm]
    _ ≤ ‖numberFieldEuclideanBasis (K := K) j • x‖ :=
      (div_le_iff₀ (rowIntegralBasisLowerDenominator_pos (K := K) (m := m))).mpr
        (by simpa [mul_comm] using hnorm)

/- [Lean infrastructure] This is the finite upper-action denominator attached
   to the fixed integral basis.  It is used only to implement the manuscript's
   permitted decrease of `C^okl` at lines 1108--1109. -/
noncomputable def rowIntegralBasisUpperDenominator {m : ℕ} : ℝ :=
  1 + rowScalarActionBoundSum (K := K) (m := m)

/- [derived consequence, paper `le:basis_of_OK`, lines 679--700] The upper
   action denominator is positive because the finite sum consists of positive
   scalar-action bounds. -/
theorem rowIntegralBasisUpperDenominator_pos {m : ℕ} :
    0 < rowIntegralBasisUpperDenominator (K := K) (m := m) := by
  rw [rowIntegralBasisUpperDenominator]
  linarith [rowScalarActionBoundSum_nonneg (K := K) (m := m)]

/- [derived consequence, paper proof of `le:crude_early`, lines 1108--1110]
   This is the manuscript's `C^okl` after it has been decreased so that its
   product with an upper comparison constant is at most one.  The minimum
   retains `le:basis_of_OK`'s lower comparison while its second term gives the
   normalized upper comparison used in the corrected square-norm estimate. -/
noncomputable def rowIntegralBasisAdjustedLowerConstant {m : ℕ} : ℝ :=
  min (rowIntegralBasisLowerConstant (K := K) (m := m))
    (rowIntegralBasisUpperDenominator (K := K) (m := m))⁻¹

/- [derived consequence, paper proof of `le:crude_early`, lines 1108--1110]
   The adjusted manuscript constant remains positive. -/
theorem rowIntegralBasisAdjustedLowerConstant_pos {m : ℕ} :
    0 < rowIntegralBasisAdjustedLowerConstant (K := K) (m := m) := by
  rw [rowIntegralBasisAdjustedLowerConstant]
  exact lt_min
    (rowIntegralBasisLowerConstant_pos (K := K) (m := m))
    (inv_pos.mpr (rowIntegralBasisUpperDenominator_pos (K := K) (m := m)))

/- [derived consequence, paper `le:basis_of_OK`, lines 679--700] Decreasing
   `C^okl` preserves its lower comparison with the integral-basis multiples. -/
theorem rowIntegralBasisAdjustedLowerConstant_lower_apply
    {m : ℕ} (j : IntegralBasisIndex K) (x : RowVector K m) :
    rowIntegralBasisAdjustedLowerConstant (K := K) (m := m) * ‖x‖ ≤
      ‖numberFieldEuclideanBasis (K := K) j • x‖ := by
  have hconstant : rowIntegralBasisAdjustedLowerConstant (K := K) (m := m) ≤
      rowIntegralBasisLowerConstant (K := K) (m := m) := by
    rw [rowIntegralBasisAdjustedLowerConstant]
    exact min_le_left _ _
  exact (mul_le_mul_of_nonneg_right hconstant (norm_nonneg _)).trans
    (rowIntegralBasisLowerConstant_apply (K := K) (m := m) j x)

/- [derived consequence, corrected paper proof of `le:crude_early`,
   lines 1108--1112] The newly imposed normalization converts the upper bound
   in `le:basis_of_OK` into the comparison actually used in line 1112:
   `C^okl ‖u_j x‖ ≤ ‖x‖`. -/
theorem rowIntegralBasisAdjustedLowerConstant_upper_apply
    {m : ℕ} (j : IntegralBasisIndex K) (x : RowVector K m) :
    rowIntegralBasisAdjustedLowerConstant (K := K) (m := m) *
        ‖numberFieldEuclideanBasis (K := K) j • x‖ ≤ ‖x‖ := by
  let B : ℝ := rowIntegralBasisUpperDenominator (K := K) (m := m)
  have hBpos : 0 < B := rowIntegralBasisUpperDenominator_pos (K := K) (m := m)
  have hcoeff : rowScalarActionBound (K := K) (m := m) j ≤ B := by
    calc
      rowScalarActionBound (K := K) (m := m) j ≤
          rowScalarActionBoundSum (K := K) (m := m) :=
        rowScalarActionBound_le_sum (K := K) (m := m) j
      _ ≤ B := by
        dsimp [B, rowIntegralBasisUpperDenominator]
        linarith
  have haction : ‖numberFieldEuclideanBasis (K := K) j • x‖ ≤ B * ‖x‖ :=
    (rowScalarActionBound_apply (K := K) (m := m) j x).trans
      (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _))
  have hconstant : rowIntegralBasisAdjustedLowerConstant (K := K) (m := m) ≤
      B⁻¹ := by
    rw [rowIntegralBasisAdjustedLowerConstant]
    change min _ (rowIntegralBasisUpperDenominator (K := K) (m := m))⁻¹ ≤ B⁻¹
    dsimp [B]
    exact min_le_right _ _
  calc
    rowIntegralBasisAdjustedLowerConstant (K := K) (m := m) *
        ‖numberFieldEuclideanBasis (K := K) j • x‖ ≤
        rowIntegralBasisAdjustedLowerConstant (K := K) (m := m) * (B * ‖x‖) :=
      mul_le_mul_of_nonneg_left haction
        (rowIntegralBasisAdjustedLowerConstant_pos (K := K) (m := m)).le
    _ ≤ B⁻¹ * (B * ‖x‖) :=
      mul_le_mul_of_nonneg_right hconstant
        (mul_nonneg hBpos.le (norm_nonneg _))
    _ = ‖x‖ := by
      rw [← mul_assoc, inv_mul_cancel₀ hBpos.ne', one_mul]

/- [derived consequence, corrected paper proof of `le:crude_early`,
   lines 1108--1112] The preceding normalized comparison in the row-span
   subtype, retaining the manuscript's `u_j v_i` notation. -/
set_option maxHeartbeats 1000000 in
theorem rowIntegralBasisAdjustedLowerConstant_upper_apply_subtype
    {m k : ℕ} (V : Grassmannian K m k)
    (j : IntegralBasisIndex K) (x : rowRealSpan V) :
    rowIntegralBasisAdjustedLowerConstant (K := K) (m := m) *
        ‖numberFieldEuclideanBasis (K := K) j • x‖ ≤ ‖x‖ := by
  change rowIntegralBasisAdjustedLowerConstant (K := K) (m := m) *
      ‖numberFieldEuclideanBasis (K := K) j • (x : RowVector K m)‖ ≤
        ‖(x : RowVector K m)‖
  exact rowIntegralBasisAdjustedLowerConstant_upper_apply (K := K) (m := m) j x

/- [derived consequence, corrected paper proof of `le:crude_early`,
   lines 1108--1112] This is the pair-indexed statement used when summing the
   corrected comparison over `j` in the manuscript's square-norm display. -/
set_option maxHeartbeats 1000000 in
theorem rowIndependentRealBasis_adjusted_norm_le
    {m k : ℕ} (V : Grassmannian K m k)
    (v : Fin k → rowZLattice V)
    (hv : LinearIndependent K (fun i => (v i : rowRealSpan V)))
    (i : Fin k) (j : IntegralBasisIndex K) :
    rowIntegralBasisAdjustedLowerConstant (K := K) (m := m) *
        ‖rowIndependentRealBasis V v hv ⟨i, j⟩‖ ≤ ‖(v i : rowRealSpan V)‖ := by
  rw [rowIndependentRealBasis_apply,
    ← numberFieldEuclideanBasis_apply (K := K) j]
  exact rowIntegralBasisAdjustedLowerConstant_upper_apply_subtype V j
    (v i : rowRealSpan V)

/- [derived consequence, corrected paper proof of `le:crude_early`,
   lines 1110--1112] Summing the normalized comparison over the fixed
   integral basis gives the square-norm inequality before division by `d`.
   The factor is kept as the cardinality of that basis until the next lemma
   identifies it with the manuscript's degree `d = [K : ℚ]`. -/
set_option maxHeartbeats 2000000 in
theorem rowIndependentRealBasis_square_sum_le
    {m k : ℕ} (V : Grassmannian K m k)
    (v : Fin k → rowZLattice V)
    (hv : LinearIndependent K (fun i => (v i : rowRealSpan V))) :
    (rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
        (∑ q : Σ _ : Fin k, IntegralBasisIndex K,
          ‖rowIndependentRealBasis V v hv q‖ ^ 2) ≤
      (Fintype.card (IntegralBasisIndex K) : ℝ) *
        ∑ i : Fin k, ‖(v i : rowRealSpan V)‖ ^ 2 := by
  classical
  letI : Fintype (IntegralBasisIndex K) := Fintype.ofFinite _
  have hc : 0 ≤ rowIntegralBasisAdjustedLowerConstant (K := K) (m := m) :=
    (rowIntegralBasisAdjustedLowerConstant_pos (K := K) (m := m)).le
  have hpoint (q : Σ _ : Fin k, IntegralBasisIndex K) :
      (rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
          ‖rowIndependentRealBasis V v hv q‖ ^ 2 ≤
        ‖(v q.1 : rowRealSpan V)‖ ^ 2 := by
    have hcomparison :
        rowIntegralBasisAdjustedLowerConstant (K := K) (m := m) *
            ‖rowIndependentRealBasis V v hv q‖ ≤
          ‖(v q.1 : rowRealSpan V)‖ :=
      rowIndependentRealBasis_adjusted_norm_le V v hv q.1 q.2
    have hsquare :
        (rowIntegralBasisAdjustedLowerConstant (K := K) (m := m) *
            ‖rowIndependentRealBasis V v hv q‖) ^ 2 ≤
          ‖(v q.1 : rowRealSpan V)‖ ^ 2 :=
      (sq_le_sq₀ (mul_nonneg hc (norm_nonneg _)) (norm_nonneg _)).mpr hcomparison
    simpa only [mul_pow] using hsquare
  have hsum :
      (∑ q : Σ _ : Fin k, IntegralBasisIndex K,
        (rowIntegralBasisAdjustedLowerConstant
        (K := K) (m := m)) ^ 2 * ‖rowIndependentRealBasis V v hv q‖ ^ 2) ≤
        ∑ q : Σ _ : Fin k, IntegralBasisIndex K, ‖(v q.1 : rowRealSpan V)‖ ^ 2 := by
    exact Finset.sum_le_sum fun q _ => hpoint q
  calc
    (rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
        (∑ q : Σ _ : Fin k, IntegralBasisIndex K,
          ‖rowIndependentRealBasis V v hv q‖ ^ 2) =
        ∑ q : Σ _ : Fin k, IntegralBasisIndex K,
          (rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
            ‖rowIndependentRealBasis V v hv q‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ ∑ q : Σ _ : Fin k, IntegralBasisIndex K,
        ‖(v q.1 : rowRealSpan V)‖ ^ 2 := hsum
    _ = (Fintype.card (IntegralBasisIndex K) : ℝ) *
        ∑ i : Fin k, ‖(v i : rowRealSpan V)‖ ^ 2 := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Finset.mul_sum]

/- [derived consequence, paper `le:basis_of_OK`, lines 679--700] The fixed
   integral-basis index has cardinality `d = [K : ℚ]`, so the preceding
   cardinality factor is exactly the manuscript's degree factor. -/
theorem integralBasisIndex_card_eq_degree :
    Fintype.card (IntegralBasisIndex K) = degree K := by
  classical
  letI : Fintype (IntegralBasisIndex K) := Fintype.ofFinite _
  rw [← Module.finrank_eq_card_chooseBasisIndex ℤ (𝓞 K),
    NumberField.RingOfIntegers.rank]
  rfl

/- [paper, corrected proof of `le:crude_early`, lines 1110--1112] This is
   precisely the second inequality in the manuscript's displayed square-norm
   estimate, with `w_ij` represented by `rowIndependentRealBasis`. -/
set_option maxHeartbeats 1000000 in
theorem rowIndependentRealBasis_square_norm_bound
    {m k : ℕ} (V : Grassmannian K m k)
    (v : Fin k → rowZLattice V)
    (hv : LinearIndependent K (fun i => (v i : rowRealSpan V))) :
    ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 /
        (degree K : ℝ)) *
        (∑ q : Σ _ : Fin k, IntegralBasisIndex K,
          ‖rowIndependentRealBasis V v hv q‖ ^ 2) ≤
      ∑ i : Fin k, ‖(v i : rowRealSpan V)‖ ^ 2 := by
  classical
  letI : Fintype (IntegralBasisIndex K) := Fintype.ofFinite _
  have hdegree_nat : 0 < degree K := by
    rw [degree]
    exact Module.finrank_pos
  have hdegree : 0 < (degree K : ℝ) := by
    exact_mod_cast hdegree_nat
  have hsum := rowIndependentRealBasis_square_sum_le V v hv
  rw [integralBasisIndex_card_eq_degree (K := K)] at hsum
  calc
    ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 /
        (degree K : ℝ)) *
        (∑ q : Σ _ : Fin k, IntegralBasisIndex K,
          ‖rowIndependentRealBasis V v hv q‖ ^ 2) =
        ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
          (∑ q : Σ _ : Fin k, IntegralBasisIndex K,
            ‖rowIndependentRealBasis V v hv q‖ ^ 2)) /
          (degree K : ℝ) := by ring
    _ ≤ ((degree K : ℝ) *
          ∑ i : Fin k, ‖(v i : rowRealSpan V)‖ ^ 2) /
          (degree K : ℝ) :=
      div_le_div_of_nonneg_right hsum hdegree.le
    _ = ∑ i : Fin k, ‖(v i : rowRealSpan V)‖ ^ 2 := by
      exact mul_div_cancel_left₀ _ hdegree.ne'

/- [paper, corrected proof of `le:crude_early`, lines 1110--1112] This is
   the complete corrected square-norm display: the rank-`k` witness supplies
   the selected rows `v_i`, and their integral-basis multiples are the
   manuscript's `w_ij`. -/
set_option maxHeartbeats 1000000 in
theorem rowMatrixZLattice_crude_square_norm_bound
    {m k n : ℕ} (V : Grassmannian K m k)
    (A : rowMatrixZLattice V n) (e : Fin k → Fin n)
    (hv : LinearIndependent K (fun i =>
      ((rowMatrixZLatticeEquiv V A (e i) : rowZLattice V) : rowRealSpan V))) :
    ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 /
        (degree K : ℝ)) *
        (∑ q : Σ _ : Fin k, IntegralBasisIndex K,
          ‖rowIndependentRealBasis V
            (fun i => rowMatrixZLatticeEquiv V A (e i)) hv q‖ ^ 2) ≤
      ‖(A : rowMatrixRealSpan V n)‖ ^ 2 := by
  have he : Function.Injective e := by
    intro i j hij
    apply hv.injective
    simpa [hij]
  exact (rowIndependentRealBasis_square_norm_bound V
      (fun i => rowMatrixZLatticeEquiv V A (e i)) hv).trans
    (rowMatrixZLattice_selectedRows_sq_sum_le V A e he)

/- [paper, proof of `le:crude_early`, lines 1114--1118] The arithmetic--
   geometric mean step for the manuscript's `kd` vectors `w_ij`.  The sigma
   index is exactly the paper's pair index `(i,j)`, and its cardinality is
   proved to be `k d` rather than absorbed into an unnamed dimension. -/
set_option maxHeartbeats 2000000 in
theorem rowIndependentRealBasis_geom_mean_le
    {m k : ℕ} (V : Grassmannian K m k) (hk : 0 < k)
    (v : Fin k → rowZLattice V)
    (hv : LinearIndependent K (fun i => (v i : rowRealSpan V))) :
    (∏ q : Σ _ : Fin k, IntegralBasisIndex K,
      ‖rowIndependentRealBasis V v hv q‖) ^
        (2 / ((k * degree K : ℕ) : ℝ)) ≤
      (1 / ((k * degree K : ℕ) : ℝ)) *
        ∑ q : Σ _ : Fin k, IntegralBasisIndex K,
          ‖rowIndependentRealBasis V v hv q‖ ^ 2 := by
  classical
  letI : Fintype (IntegralBasisIndex K) := Fintype.ofFinite _
  have hdegree_nat : 0 < degree K := by
    rw [degree]
    exact Module.finrank_pos
  have hcard : Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) =
      k * degree K := by
    simpa [Fintype.card_sigma, integralBasisIndex_card_eq_degree (K := K)]
  have hcard_pos : 0 < Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) := by
    rw [hcard]
    exact Nat.mul_pos hk hdegree_nat
  have hweights : 0 < ∑ _ : (Σ _ : Fin k, IntegralBasisIndex K), (1 : ℝ) := by
    have hcard_pos_R : (0 : ℝ) <
        Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) := by
      exact_mod_cast hcard_pos
    simpa using hcard_pos_R
  have hgeom := Real.geom_mean_le_arith_mean
    (Finset.univ : Finset (Σ _ : Fin k, IntegralBasisIndex K))
    (fun _ => (1 : ℝ)) (fun q => ‖rowIndependentRealBasis V v hv q‖ ^ 2)
    (by intro q hq; norm_num)
    hweights
    (by intro q hq; exact sq_nonneg (‖rowIndependentRealBasis V v hv q‖))
  have hgeom' :
      (∏ q : Σ _ : Fin k, IntegralBasisIndex K,
        ‖rowIndependentRealBasis V v hv q‖ ^ 2) ^
          (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ)⁻¹ ≤
        (∑ q : Σ _ : Fin k, IntegralBasisIndex K,
          ‖rowIndependentRealBasis V v hv q‖ ^ 2) /
          (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) := by
    simpa only [Real.rpow_one, one_mul, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one] using hgeom
  rw [hcard] at hgeom'
  have hprod_nonneg : 0 ≤ ∏ q : Σ _ : Fin k, IntegralBasisIndex K,
      ‖rowIndependentRealBasis V v hv q‖ :=
    Finset.prod_nonneg fun q _ => norm_nonneg _
  have hprod :
      (∏ q : Σ _ : Fin k, IntegralBasisIndex K,
        ‖rowIndependentRealBasis V v hv q‖ ^ 2) =
      (∏ q : Σ _ : Fin k, IntegralBasisIndex K,
        ‖rowIndependentRealBasis V v hv q‖) ^ 2 := by
    rw [← Finset.prod_pow]
  calc
    (∏ q : Σ _ : Fin k, IntegralBasisIndex K, ‖rowIndependentRealBasis V v hv q‖) ^
        (2 / ((k * degree K : ℕ) : ℝ)) =
        ((∏ q : Σ _ : Fin k, IntegralBasisIndex K,
          ‖rowIndependentRealBasis V v hv q‖) ^ 2) ^
            (((k * degree K : ℕ) : ℝ)⁻¹) := by
      rw [div_eq_mul_inv]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
      exact Real.rpow_natCast_mul hprod_nonneg 2
        (((k * degree K : ℕ) : ℝ)⁻¹)
    _ = (∏ q : Σ _ : Fin k, IntegralBasisIndex K,
        ‖rowIndependentRealBasis V v hv q‖ ^ 2) ^
          (((k * degree K : ℕ) : ℝ)⁻¹) := by
      rw [hprod]
    _ ≤ (∑ q : Σ _ : Fin k, IntegralBasisIndex K,
        ‖rowIndependentRealBasis V v hv q‖ ^ 2) /
          ((k * degree K : ℕ) : ℝ) := hgeom'
    _ = (1 / ((k * degree K : ℕ) : ℝ)) *
        ∑ q : Σ _ : Fin k, IntegralBasisIndex K,
          ‖rowIndependentRealBasis V v hv q‖ ^ 2 := by
      ring

/- [derived consequence, paper proof of `le:crude_early`, lines 1104--1116]
   The free `𝓞_K`-module generated by the selected rows is a sublattice of
   `Λ_D`; applying the paper's Hadamard bound to its displayed `w_ij` basis
   gives the required comparison with `H(D)`. -/
theorem rowSpaceHeight_le_prod_norm_rowIndependentRealBasis
    {m k : ℕ} (V : Grassmannian K m k) (hk : 0 < k)
    (v : Fin k → rowZLattice V)
    (hv : LinearIndependent K (fun i => (v i : rowRealSpan V))) :
    rowSpaceHeight V ≤ ∏ q : Σ _ : Fin k, IntegralBasisIndex K,
      ‖rowIndependentRealBasis V v hv q‖ := by
  letI : Fintype (IntegralBasisIndex K) := Fintype.ofFinite _
  letI : MeasurableSpace (rowRealSpan V) :=
    @Subtype.instMeasurableSpace (RowVector K m)
      (fun x => x ∈ rowRealSpan V) (rowVectorMeasurableSpace (K := K))
  letI : BorelSpace (rowRealSpan V) :=
    @Subtype.borelSpace (RowVector K m) _ (rowVectorMeasurableSpace (K := K))
      (rowVectorBorelSpace (K := K)) (fun x => x ∈ rowRealSpan V)
  letI : NormedSpace ℝ (rowRealSpan V) :=
    Submodule.normedSpace (rowRealSpan V)
  letI : InnerProductSpace ℝ (rowRealSpan V) :=
    Submodule.innerProductSpace (rowRealSpan V)
  letI : Nontrivial (rowRealSpan V) := by
    exact Module.nontrivial_of_finrank_pos (R := ℝ) (M := rowRealSpan V) (by
      rw [rowRealSpan_finrank V]
      exact Nat.mul_pos hk Module.finrank_pos)
  rw [rowSpaceHeight_eq_volume_covolume]
  apply ZLattice.covolume_le_prod_norm_of_fintype_real_basis_mem
  rintro ⟨i, j⟩
  exact rowIndependentRealBasis_mem_rowZLattice V v hv i j

/- [Lean infrastructure] The scalar rearrangement used to divide the
   corrected square-norm inequality by `(C^okl)^2 k`.  Keeping it separate
   prevents elementary denominator clearing from unfolding the manuscript's
   `w_ij` sum. -/
theorem crudeMeanDivision
    {c d k s a : ℝ} (hc : 0 < c) (hd : 0 < d) (hk : 0 < k)
    (h : (c ^ 2 / d) * s ≤ a) :
    (1 / (k * d)) * s ≤ a / (c ^ 2 * k) := by
  have hdenom : 0 ≤ c ^ 2 * k := by positivity
  calc
    (1 / (k * d)) * s = ((c ^ 2 / d) * s) / (c ^ 2 * k) := by
      field_simp [hc.ne', hd.ne', hk.ne']
    _ ≤ a / (c ^ 2 * k) := div_le_div_of_nonneg_right h hdenom

/- [Lean infrastructure] Raising the manuscript's positive `2/(kd)` root
   inequality back to its natural-power form.  This is only real-power
   bookkeeping for the final sentence of `le:crude_early`. -/
theorem le_pow_of_rpow_le_sq
    {x y : ℝ} {N : ℕ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hN : 0 < N)
    (h : x ^ (2 / (N : ℝ)) ≤ y ^ 2) :
    x ≤ y ^ N := by
  have hN_R : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hraise := Real.rpow_le_rpow (Real.rpow_nonneg hx _) h
    (by positivity : 0 ≤ (N : ℝ) / 2)
  calc
    x = x ^ ((2 / (N : ℝ)) * ((N : ℝ) / 2)) := by
      rw [show (2 / (N : ℝ)) * ((N : ℝ) / 2) = 1 by
        field_simp [hN_R.ne']]
      exact (Real.rpow_one x).symm
    _ = (x ^ (2 / (N : ℝ))) ^ ((N : ℝ) / 2) :=
      Real.rpow_mul hx _ _
    _ ≤ (y ^ 2) ^ ((N : ℝ) / 2) := hraise
    _ = y ^ N := by
      calc
        (y ^ 2) ^ ((N : ℝ) / 2) = y ^ ((2 : ℝ) * ((N : ℝ) / 2)) := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
          exact (Real.rpow_natCast_mul hy 2 ((N : ℝ) / 2)).symm
        _ = y ^ (N : ℝ) := by
          congr 1
          field_simp [hN_R.ne']
        _ = y ^ N := Real.rpow_natCast y N

/- [derived consequence, corrected paper proof of `le:crude_early`,
   lines 1112--1118] Divide the corrected square-norm estimate by the
   positive factor `(C^okl)^2 k`.  This is the middle comparison between the
   arithmetic mean of the manuscript's `w_ij` and the witness norm. -/
set_option maxHeartbeats 1000000 in
theorem rowMatrixZLattice_crude_mean_bound
    {m k n : ℕ} (V : Grassmannian K m k)
    (A : rowMatrixZLattice V n) (e : Fin k → Fin n)
    (hk : 0 < k)
    (hv : LinearIndependent K (fun i =>
      ((rowMatrixZLatticeEquiv V A (e i) : rowZLattice V) : rowRealSpan V))) :
    (1 / ((k * degree K : ℕ) : ℝ)) *
        (∑ q : Σ _ : Fin k, IntegralBasisIndex K,
          ‖rowIndependentRealBasis V
            (fun i => rowMatrixZLatticeEquiv V A (e i)) hv q‖ ^ 2) ≤
      ‖(A : rowMatrixRealSpan V n)‖ ^ 2 /
        ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
          (k : ℝ)) := by
  classical
  letI : Fintype (IntegralBasisIndex K) := Fintype.ofFinite _
  have hkR : 0 < (k : ℝ) := by
    exact_mod_cast hk
  have hdegree_nat : 0 < degree K := by
    rw [degree]
    exact Module.finrank_pos
  have hdegreeR : 0 < (degree K : ℝ) := by
    exact_mod_cast hdegree_nat
  have hc : 0 < rowIntegralBasisAdjustedLowerConstant (K := K) (m := m) :=
    rowIntegralBasisAdjustedLowerConstant_pos (K := K) (m := m)
  have hdenom : 0 ≤
      (rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
        (k : ℝ) := by
    positivity
  have hsq := rowMatrixZLattice_crude_square_norm_bound V A e hv
  have hdivision := crudeMeanDivision hc hdegreeR hkR hsq
  simpa only [Nat.cast_mul] using hdivision

/- [paper, corrected proof of `le:crude_early`, lines 1112--1118] This is
   the paper's complete height-root chain for a full-rank witness matrix:
   corrected square norms, AM--GM over the actual `w_ij`, Hadamard, and the
   lattice-height comparison. -/
set_option maxHeartbeats 1500000 in
theorem rowMatrixZLattice_height_rpow_le
    {m k n : ℕ} (V : Grassmannian K m k)
    (A : rowMatrixZLattice V n) (e : Fin k → Fin n)
    (hk : 0 < k)
    (hv : LinearIndependent K (fun i =>
      ((rowMatrixZLatticeEquiv V A (e i) : rowZLattice V) : rowRealSpan V))) :
    (rowSpaceHeight V) ^ (2 / ((k * degree K : ℕ) : ℝ)) ≤
      ‖(A : rowMatrixRealSpan V n)‖ ^ 2 /
        ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
          (k : ℝ)) := by
  classical
  letI : Fintype (IntegralBasisIndex K) := Fintype.ofFinite _
  have hheight := rowSpaceHeight_le_prod_norm_rowIndependentRealBasis V hk
    (fun i => rowMatrixZLatticeEquiv V A (e i)) hv
  have hexponent_nonneg : 0 ≤ 2 / ((k * degree K : ℕ) : ℝ) := by
    positivity
  have hheight_rpow := Real.rpow_le_rpow (rowSpaceHeight_pos V).le hheight
    hexponent_nonneg
  have hgeom := rowIndependentRealBasis_geom_mean_le V hk
    (fun i => rowMatrixZLatticeEquiv V A (e i)) hv
  have hmean := rowMatrixZLattice_crude_mean_bound V A e hk hv
  exact hheight_rpow.trans (hgeom.trans hmean)

/- [derived consequence, corrected paper proof of `le:crude_early`,
   lines 1118--1120] This is the natural-power conclusion of the displayed
   root-height chain before substituting the support bound `‖A‖ ≤ Csup T`. -/
set_option maxHeartbeats 1500000 in
theorem rowMatrixZLattice_height_le_normPower
    {m k n : ℕ} (V : Grassmannian K m k)
    (A : rowMatrixZLattice V n) (e : Fin k → Fin n)
    (hk : 0 < k)
    (hv : LinearIndependent K (fun i =>
      ((rowMatrixZLatticeEquiv V A (e i) : rowZLattice V) : rowRealSpan V))) :
    rowSpaceHeight V ≤
      (‖(A : rowMatrixRealSpan V n)‖ /
        Real.sqrt ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
          (k : ℝ))) ^ (k * degree K) := by
  classical
  letI : Fintype (IntegralBasisIndex K) := Fintype.ofFinite _
  have hkR : 0 < (k : ℝ) := by
    exact_mod_cast hk
  have hc : 0 < rowIntegralBasisAdjustedLowerConstant (K := K) (m := m) :=
    rowIntegralBasisAdjustedLowerConstant_pos (K := K) (m := m)
  have hratio :
      ‖(A : rowMatrixRealSpan V n)‖ ^ 2 /
          ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
            (k : ℝ)) =
        (‖(A : rowMatrixRealSpan V n)‖ /
          Real.sqrt ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
            (k : ℝ))) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
  have hroot := rowMatrixZLattice_height_rpow_le V A e hk hv
  rw [hratio] at hroot
  apply le_pow_of_rpow_le_sq (rowSpaceHeight_pos V).le
    (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  · exact Nat.mul_pos hk (by
      rw [degree]
      exact Module.finrank_pos)
  · exact hroot

/- [paper, definition in the proof of `le:crude_early`, line 1120] The
   manuscript's displayed constant `C^crude2`, with the adjusted
   `C^okl` from lines 1108--1109 retained in its denominator. -/
noncomputable def Ccrude2 {m k : ℕ} (Csup : ℝ) : ℝ :=
  (Csup /
    Real.sqrt ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
      (k : ℝ))) ^ (k * degree K)

/- [derived consequence, paper `le:crude_early`, lines 1093--1097 and 1120]
   The displayed crude-height constant is positive when `Csup > 0`. -/
theorem Ccrude2_pos
    {m k : ℕ} (Csup : ℝ) (hCsup : 0 < Csup) (hk : 0 < k) :
    0 < Ccrude2 (K := K) (m := m) (k := k) Csup := by
  rw [Ccrude2]
  have hc : 0 < rowIntegralBasisAdjustedLowerConstant (K := K) (m := m) :=
    rowIntegralBasisAdjustedLowerConstant_pos (K := K) (m := m)
  have hkR : 0 < (k : ℝ) := by
    exact_mod_cast hk
  apply pow_pos
  exact div_pos hCsup (Real.sqrt_pos.2 (by positivity))

/- [derived consequence, corrected paper proof of `le:crude_early`,
   lines 1118--1120] Substitute the witness norm bound in the natural-power
   height inequality.  The conclusion retains the exact `C^crude2 T^(kd)`
   expression displayed by the manuscript. -/
set_option maxHeartbeats 1500000 in
theorem rowMatrixZLattice_height_le_Ccrude2
    {m k n : ℕ} (V : Grassmannian K m k)
    (A : rowMatrixZLattice V n) (e : Fin k → Fin n)
    (hk : 0 < k)
    (hv : LinearIndependent K (fun i =>
      ((rowMatrixZLatticeEquiv V A (e i) : rowZLattice V) : rowRealSpan V)))
    (Csup T : ℝ)
    (hAnorm : ‖(A : rowMatrixRealSpan V n)‖ ≤ Csup * T) :
    rowSpaceHeight V ≤
      Ccrude2 (K := K) (m := m) (k := k) Csup * T ^ (k * degree K) := by
  classical
  letI : Fintype (IntegralBasisIndex K) := Fintype.ofFinite _
  have hnorm := rowMatrixZLattice_height_le_normPower V A e hk hv
  have hbase :
      ‖(A : rowMatrixRealSpan V n)‖ /
          Real.sqrt ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
            (k : ℝ)) ≤
        (Csup * T) /
          Real.sqrt ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
            (k : ℝ)) :=
    div_le_div_of_nonneg_right hAnorm (Real.sqrt_nonneg _)
  calc
    rowSpaceHeight V ≤
        (‖(A : rowMatrixRealSpan V n)‖ /
          Real.sqrt ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
            (k : ℝ))) ^ (k * degree K) := hnorm
    _ ≤ ((Csup * T) /
          Real.sqrt ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
            (k : ℝ))) ^ (k * degree K) :=
      pow_le_pow_left₀
        (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hbase _
    _ = (Csup /
          Real.sqrt ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
            (k : ℝ))) ^ (k * degree K) * T ^ (k * degree K) := by
      rw [show (Csup * T) /
          Real.sqrt ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
            (k : ℝ)) =
          (Csup /
            Real.sqrt ((rowIntegralBasisAdjustedLowerConstant (K := K) (m := m)) ^ 2 *
              (k : ℝ))) * T by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring, mul_pow]
    _ = Ccrude2 (K := K) (m := m) (k := k) Csup * T ^ (k * degree K) := rfl

/- [paper, lemma `le:crude_early`, lines 1091--1120] The manuscript-facing
   conclusion: membership in the exact echelon family `𝓕_k(T)` supplies the
   rank-`k` witness to which the preceding selected-row argument applies. -/
set_option maxHeartbeats 1500000 in
theorem echelon_mem_calF_height_le_Ccrude2
    {m k n : ℕ} (D : EchelonMatrix K k m) (Csup T : ℝ) (hk : 0 < k)
    (hD : D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T) :
    rowSpaceHeight (echelonRowSpace D) ≤
      Ccrude2 (K := K) (m := m) (k := k) Csup * T ^ (k * degree K) := by
  rcases (mem_calF_iff.mp hD) with ⟨A, hArank, hAnorm⟩
  obtain ⟨e, hv⟩ := exists_linearIndependent_rows_of_rowMatrixRank_eq
    (echelonRowSpace D) A hArank
  change ‖(A : rowMatrixRealSpan (echelonRowSpace D) n)‖ ≤ Csup * T at hAnorm
  exact rowMatrixZLattice_height_le_Ccrude2 (echelonRowSpace D) A e hk hv
    Csup T hAnorm

end SelectedRows

end Katznelson
