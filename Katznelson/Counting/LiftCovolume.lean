import Katznelson.Counting.MainTermNormalization
import Katznelson.Counting.FiniteField
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Covolume of normalized lifts

This module formalizes the lattice setup in `papers/katznelson.tex`, lines
1816--1827, including the assertion that every normalized lift has covolume
one.  The checked-in TeX source is authoritative.

Provenance:

* `paper`: the raw lift, normalization, and unit-covolume statements refer to
  the manuscript's equation `eq:def_of_L` and lines 1816--1827.
* `derived consequence`: the quotient-index and determinant calculations are
  proved from the paper definitions and standard Mathlib lattice theorems.
* `Lean infrastructure`: the one-column embedding, scalar pullback, and
  topology bridges only represent the paper's objects in the ambient matrix
  space.  The Euclidean-to-manuscript measure bridge is the existing,
  attributed result in `MainTermNormalization`.

No external theorem is used as an axiom here; all cited arithmetic and
measure interfaces are either imported with their source comments or proved
in this development.
-/

namespace Katznelson

open Set
open MeasureTheory
open NumberField
open scoped BigOperators NumberField

variable {K : Type*} [Field K] [NumberField K]

noncomputable def reduceAddHom (P : PrimeIdeal K) {n : ℕ} :
    (Fin n → 𝓞 K) →+ (Fin n → residueField P) where
  toFun := reduce P
  map_zero' := by ext i; simp [reduce]
  map_add' x y := by ext i; simp [reduce]

noncomputable def rawLiftQuotientHom (P : PrimeIdeal K) {n s : ℕ}
    (S : Code P n s) :
    (Fin n → 𝓞 K) →+ ((Fin n → residueField P) ⧸ S.1) :=
  (S.1.mkQ.toAddMonoidHom).comp (reduceAddHom P)

theorem rawLiftQuotientHom_ker (P : PrimeIdeal K) {n s : ℕ}
    (S : Code P n s) :
    (rawLiftQuotientHom P S).ker = (rawLift P S).toAddSubgroup := by
  ext x
  change S.1.mkQ (reduce P x) = 0 ↔ x ∈ rawLift P S
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

theorem rawLiftQuotientHom_surjective (P : PrimeIdeal K) {n s : ℕ}
    (S : Code P n s) :
    Function.Surjective (rawLiftQuotientHom P S) := by
  intro z
  obtain ⟨y, hy⟩ := S.1.mkQ_surjective z
  obtain ⟨x, hx⟩ := reduce_surjective P n y
  refine ⟨x, ?_⟩
  change S.1.mkQ (reduce P x) = z
  rw [hx, hy]

/- [derived consequence of paper equation `eq:def_of_L`, lines 1816--1827]
The quotient map computes the exact finite index of a raw lift. -/
theorem rawLift_index (P : PrimeIdeal K) {n s : ℕ}
    (S : Code P n s) :
    (rawLift P S).toAddSubgroup.index = idealNorm P ^ (n - s) := by
  rw [← rawLiftQuotientHom_ker P S, AddSubgroup.index_ker]
  have hrange : (rawLiftQuotientHom P S).range = ⊤ :=
    (AddMonoidHom.range_eq_top.mpr (rawLiftQuotientHom_surjective P S))
  rw [hrange, AddSubgroup.card_top]
  rw [Module.natCard_eq_pow_finrank (K := residueField P)]
  rw [Submodule.finrank_quotient]
  rw [show Module.finrank (residueField P) (Fin n → residueField P) = n by simp]
  rw [S.2]
  rw [← Fintype.card_eq_nat_card, card_residueField_eq_idealNorm]

noncomputable def integralColumnEmbedding (n : ℕ) :
    (Fin n → 𝓞 K) →ₗ[ℤ] M n 1 (K_ℝ[K]) where
  toFun x i j := numberEmbedding K (x i)
  map_add' x y := by
    ext i j
    exact numberEmbedding_add K _ _
  map_smul' a x := by
    ext i j
    change numberEmbedding K (a • (x i : K)) = a • numberEmbedding K (x i : K)
    exact numberEmbedding_zsmul K a (x i : K)

theorem integralColumnEmbedding_injective {n : ℕ} :
    Function.Injective (@integralColumnEmbedding K _ _ n) := by
  intro x y h
  funext i
  apply NumberField.RingOfIntegers.coe_injective
  exact numberEmbedding_injective K (congrArg (fun z => z i 0) h)

noncomputable def embeddedRawLift (P : PrimeIdeal K) {n s : ℕ}
    (S : Code P n s) : Submodule ℤ (M n 1 (K_ℝ[K])) :=
  ((rawLift P S).restrictScalars ℤ).map (integralColumnEmbedding (K := K) n)

theorem embeddedRawLift_le_ambient (P : PrimeIdeal K) {n s : ℕ}
    (S : Code P n s) :
    embeddedRawLift P S ≤ embeddedIntegralCoefficientLattice (K := K) n 1 := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  apply (mem_embeddedIntegralCoefficientLattice_iff (K := K)
    (integralColumnEmbedding (K := K) _ y)).2
  intro i j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rw [NumberField.mixedEmbedding.euclidean.integerLattice]
  change NumberField.mixedEmbedding.euclidean.toMixed K
      (numberEmbedding K (y i)) ∈
    NumberField.mixedEmbedding.integerLattice K
  exact ⟨y i, by simp [numberEmbedding]⟩

theorem embeddedColumnTop_eq_ambient (n : ℕ) :
    ((⊤ : Submodule (𝓞 K) (Fin n → 𝓞 K)).restrictScalars ℤ).map
        (integralColumnEmbedding (K := K) n) =
      embeddedIntegralCoefficientLattice (K := K) n 1 := by
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    apply (mem_embeddedIntegralCoefficientLattice_iff (K := K)
      (integralColumnEmbedding (K := K) _ y)).2
    intro i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rw [NumberField.mixedEmbedding.euclidean.integerLattice]
    change NumberField.mixedEmbedding.euclidean.toMixed K
        (numberEmbedding K (y i)) ∈
      NumberField.mixedEmbedding.integerLattice K
    exact ⟨y i, by simp [numberEmbedding]⟩
  · intro hx
    change x ∈ embeddedIntegralCoefficientLattice (K := K) n 1 at hx
    rcases hx with ⟨C, -, rfl⟩
    refine ⟨(fun i => C i 0), trivial, ?_⟩
    ext i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl

theorem embeddedRawLift_relIndex (P : PrimeIdeal K) {n s : ℕ}
    (S : Code P n s) :
    (embeddedRawLift P S).toAddSubgroup.relIndex
        (embeddedIntegralCoefficientLattice (K := K) n 1).toAddSubgroup =
      idealNorm P ^ (n - s) := by
  rw [← embeddedColumnTop_eq_ambient (K := K) n]
  change
    (((rawLift P S).restrictScalars ℤ).map
        (integralColumnEmbedding (K := K) n)).toAddSubgroup.relIndex
      (((⊤ : Submodule (𝓞 K) (Fin n → 𝓞 K)).restrictScalars ℤ).map
        (integralColumnEmbedding (K := K) n)).toAddSubgroup = _
  rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective]
  · change (rawLift P S).toAddSubgroup.relIndex ⊤ = _
    rw [AddSubgroup.relIndex_top_right, rawLift_index]
  · exact integralColumnEmbedding_injective (K := K)

theorem embeddedRawLift_span_top (P : PrimeIdeal K) {n s : ℕ}
    (S : Code P n s) :
    Submodule.span ℝ (embeddedRawLift P S : Set (M n 1 (K_ℝ[K]))) = ⊤ := by
  letI : NeZero P.1 := ⟨P.2.2⟩
  let q : ℕ := Ideal.absNorm (Ideal.under ℤ P.1)
  have hqprime : q.Prime := by
    dsimp [q]
    exact Nat.absNorm_under_prime P.1
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast hqprime.pos
  have hqmem : (q : 𝓞 K) ∈ P.1 := by
    dsimp [q]
    exact Int.absNorm_under_mem P.1
  apply le_antisymm
  · calc
      Submodule.span ℝ (embeddedRawLift P S : Set (M n 1 (K_ℝ[K]))) ≤
          Submodule.span ℝ
            (embeddedIntegralCoefficientLattice (K := K) n 1 :
              Set (M n 1 (K_ℝ[K]))) := by
        refine @Submodule.span_mono ℝ (M n 1 (K_ℝ[K])) _ _ _
          (embeddedRawLift P S : Set (M n 1 (K_ℝ[K])))
          (embeddedIntegralCoefficientLattice (K := K) n 1 :
            Set (M n 1 (K_ℝ[K]))) ?_
        intro x hx
        exact embeddedRawLift_le_ambient P S hx
      _ = ⊤ := embeddedIntegralCoefficientLattice_span_top (K := K) n 1
  · rw [← embeddedIntegralCoefficientLattice_span_top (K := K) n 1]
    apply Submodule.span_le.2
    intro x hx
    rcases hx with ⟨C, -, rfl⟩
    let y : Fin n → 𝓞 K := fun i => C i 0
    have hy : (q : ℤ) • y ∈ rawLift P S := by
      apply primePowerVectors_le_rawLift P S
      intro i
      simpa [y, Pi.smul_apply, smul_eq_mul, mul_comm] using
        P.1.smul_mem (y i) hqmem
    have heq : (q : ℝ) • integralMatrixEmbedding (K := K) n 1 C =
        integralColumnEmbedding (K := K) n ((q : ℤ) • y) := by
      ext i j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change (q : ℝ) • numberEmbedding K (C i 0 : K) =
        numberEmbedding K (((q : ℤ) • C i 0 : 𝓞 K) : K)
      change (q : ℝ) • numberEmbedding K (C i 0 : K) =
        numberEmbedding K ((q : ℤ) • (C i 0 : K))
      rw [numberEmbedding_zsmul]
      rw [Nat.cast_smul_eq_nsmul]
      simp
    have hqmem' : (q : ℝ) • integralMatrixEmbedding (K := K) n 1 C ∈
        Submodule.span ℝ (embeddedRawLift P S : Set (M n 1 (K_ℝ[K]))) := by
      rw [heq]
      apply Submodule.subset_span
      exact ⟨(q : ℤ) • y, hy, rfl⟩
    have hinv := (Submodule.span ℝ
        (embeddedRawLift P S : Set (M n 1 (K_ℝ[K])))).smul_mem
        (q : ℝ)⁻¹ hqmem'
    simpa [smul_smul, hqpos.ne'] using hinv

theorem embeddedRawLift_discreteTopology
    (P : PrimeIdeal K) {n s : ℕ} (S : Code P n s) :
    DiscreteTopology (embeddedRawLift P S) := by
  let toAmbient : embeddedRawLift P S →
      embeddedIntegralCoefficientLattice (K := K) n 1 :=
    fun x => ⟨x.1, embeddedRawLift_le_ambient P S x.2⟩
  apply DiscreteTopology.of_continuous_injective (f := toAmbient)
  · apply Continuous.subtype_mk
    exact continuous_subtype_val
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : embeddedIntegralCoefficientLattice (K := K) n 1 => z.1) hxy

noncomputable instance embeddedRawLift.discreteTopology
    (P : PrimeIdeal K) {n s : ℕ} (S : Code P n s) :
    DiscreteTopology (embeddedRawLift P S) :=
  embeddedRawLift_discreteTopology P S

theorem embeddedRawLift_isZLattice
    (P : PrimeIdeal K) {n s : ℕ} (S : Code P n s) :
    @IsZLattice ℝ inferInstance (M n 1 (K_ℝ[K])) inferInstance inferInstance
      (embeddedRawLift P S) (embeddedRawLift_discreteTopology P S) := by
  exact @IsZLattice.mk ℝ inferInstance (M n 1 (K_ℝ[K])) inferInstance
    inferInstance (embeddedRawLift P S)
    (embeddedRawLift_discreteTopology P S)
    (embeddedRawLift_span_top P S)

theorem embeddedRawLift_covolume_paperMatrixMeasure
    (P : PrimeIdeal K) {n s : ℕ} (S : Code P n s) :
    ZLattice.covolume (embeddedRawLift P S)
        (paperMatrixMeasure (K := K) n 1) =
      (idealNorm P : ℝ) ^ (n - s) := by
  let L₁ := embeddedRawLift P S
  let L₂ := embeddedIntegralCoefficientLattice (K := K) n 1
  let disc₁ : DiscreteTopology L₁ := by
    dsimp only [L₁]
    exact embeddedRawLift_discreteTopology P S
  let z₁ : @IsZLattice ℝ inferInstance (M n 1 (K_ℝ[K]))
      inferInstance inferInstance L₁ disc₁ := by
    dsimp only [L₁]
    exact @embeddedRawLift_isZLattice K _ _ P n s S
  let disc₂ : DiscreteTopology L₂ :=
    embeddedIntegralCoefficientLattice.discreteTopology (K := K) n 1
  let z₂ : @IsZLattice ℝ inferInstance (M n 1 (K_ℝ[K]))
      inferInstance inferInstance L₂ disc₂ :=
    embeddedIntegralCoefficientLattice.isZLattice (K := K) n 1
  let mu : Measure (M n 1 (K_ℝ[K])) :=
    coefficientMatrixEuclideanMeasure (K := K) n 1
  let vol₀ : @Measure (M n 1 (K_ℝ[K]))
      (kRealMatrixMeasurableSpace (K := K)) :=
    @volume (M n 1 (K_ℝ[K]))
      (@measureSpaceOfInnerProductSpace (M n 1 (K_ℝ[K])) inferInstance
        (mainTermMatrixInnerProductSpace (K := K)) inferInstance
        (kRealMatrixMeasurableSpace (K := K))
        (kRealMatrixBorelSpace (K := K)))
  letI : Measure.IsAddHaarMeasure mu := by
    dsimp only [mu]
    exact coefficientMatrixEuclideanMeasure_isAddHaarMeasure (K := K) n 1
  have hle : L₁ ≤ L₂ := by
    dsimp only [L₁, L₂]
    exact embeddedRawLift_le_ambient P S
  have hmu : mu = vol₀ := by
    dsimp only [mu, coefficientMatrixEuclideanMeasure, vol₀]
    exact @InnerProductSpace.euclideanHausdorffMeasure_eq_volume
      (M n 1 (K_ℝ[K])) inferInstance
      (mainTermMatrixInnerProductSpace (K := K))
      (kRealMatrixMeasurableSpace (K := K))
      (kRealMatrixBorelSpace (K := K)) inferInstance
  have hratio : ZLattice.covolume L₁ mu / ZLattice.covolume L₂ mu =
      (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) := by
    rw [hmu]
    exact @ZLattice.covolume_div_covolume_eq_relIndex'
      (M n 1 (K_ℝ[K])) inferInstance
      (mainTermMatrixInnerProductSpace (K := K)) inferInstance
      (kRealMatrixMeasurableSpace (K := K))
      (kRealMatrixBorelSpace (K := K))
      L₁ L₂ disc₁ z₁ disc₂ z₂ hle
  have hindex : L₁.toAddSubgroup.relIndex L₂.toAddSubgroup =
      idealNorm P ^ (n - s) := by
    dsimp only [L₁, L₂]
    exact embeddedRawLift_relIndex P S
  have hscale : ZLattice.covolume L₁
      (paperMatrixMeasure (K := K) n 1) =
      (paperMatrixMeasureScale (K := K) n 1 : ℝ) *
        ZLattice.covolume L₁ mu := by
    rw [paperMatrixMeasure]
    exact @covolume_nnreal_smul_measure
      (M n 1 (K_ℝ[K])) inferInstance inferInstance inferInstance
      (kRealMatrixMeasurableSpace (K := K))
      (kRealMatrixBorelSpace (K := K)) L₁ disc₁ z₁ mu
      (coefficientMatrixEuclideanMeasure_isAddHaarMeasure (K := K) n 1)
      (paperMatrixMeasureScale (K := K) n 1)
      (paperMatrixMeasureScale_pos (K := K) n 1).ne'
  rw [hscale]
  change (ZLattice.covolume L₂ mu)⁻¹ * ZLattice.covolume L₁ mu =
    (idealNorm P : ℝ) ^ (n - s)
  rw [mul_comm]
  change ZLattice.covolume L₁ mu / ZLattice.covolume L₂ mu = _
  rw [hratio, hindex, Nat.cast_pow]

theorem matrix_finrank_one (n : ℕ) :
    Module.finrank ℝ (M n 1 (K_ℝ[K])) = n * degree K := by
  rw [Module.finrank_matrix]
  simp [NumberField.mixedEmbedding.euclidean.finrank, degree]

noncomputable def scalarLinearMap (c : ℝ) (n : ℕ) :
    M n 1 (K_ℝ[K]) →ₗ[ℝ] M n 1 (K_ℝ[K]) :=
  c • LinearMap.id

/- [Lean infrastructure] The Euclidean mixed-space topology is transported
through Mathlib's `WithLp` realization.  These compatibility proofs are
needed only to apply the standard continuous-linear-equivalence covolume
formula to the manuscript's scalar normalization. -/
theorem kReal_isTopologicalAddGroup :
    IsTopologicalAddGroup K_ℝ[K] := by
  letI : Fintype {w : InfinitePlace K // w.IsReal} := Fintype.ofFinite _
  letI : Fintype {w : InfinitePlace K // w.IsComplex} := Fintype.ofFinite _
  let α := EuclideanSpace ℝ {w : InfinitePlace K // w.IsReal}
  let β := EuclideanSpace ℂ {w : InfinitePlace K // w.IsComplex}
  change IsTopologicalAddGroup (WithLp 2 (α × β))
  letI : ContinuousAdd α := by dsimp [α]; infer_instance
  letI : ContinuousAdd β := by dsimp [β]; infer_instance
  letI : ContinuousNeg α := by dsimp [α]; infer_instance
  letI : ContinuousNeg β := by dsimp [β]; infer_instance
  letI : ContinuousAdd (α × β) := Prod.continuousAdd
  letI : ContinuousNeg (α × β) := Prod.continuousNeg
  let hadd : ContinuousAdd (WithLp 2 (α × β)) := ⟨by
      change Continuous (fun p : WithLp 2 (α × β) × WithLp 2 (α × β) =>
        p.1 + p.2)
      dsimp [α, β]
      let h : Continuous (fun p : WithLp 2 (α × β) × WithLp 2 (α × β) =>
          (p.1.ofLp + p.2.ofLp)) := by
        let hf : Continuous (fun p : WithLp 2 (α × β) × WithLp 2 (α × β) =>
            p.1.ofLp) :=
          (WithLp.prod_continuous_ofLp 2 α β).comp continuous_fst
        let hg : Continuous (fun p : WithLp 2 (α × β) × WithLp 2 (α × β) =>
            p.2.ofLp) :=
          (WithLp.prod_continuous_ofLp 2 α β).comp continuous_snd
        simpa [Function.comp_def] using continuous_add.comp (hf.prodMk hg)
      exact (WithLp.prod_continuous_toLp 2 α β).comp h⟩
  let hneg : ContinuousNeg (WithLp 2 (α × β)) := ⟨by
      change Continuous (fun x : WithLp 2 (α × β) => -x)
      dsimp [α, β]
      let h : Continuous (fun x : WithLp 2 (α × β) => -x.ofLp) := by
        exact (Prod.continuousNeg.continuous_neg).comp
          (WithLp.prod_continuous_ofLp 2 α β)
      exact (WithLp.prod_continuous_toLp 2 α β).comp h⟩
  letI := hadd
  letI := hneg
  exact IsTopologicalAddGroup.mk

theorem kReal_continuousSMul :
    ContinuousSMul ℝ K_ℝ[K] := by
  letI : Fintype {w : InfinitePlace K // w.IsReal} := Fintype.ofFinite _
  letI : Fintype {w : InfinitePlace K // w.IsComplex} := Fintype.ofFinite _
  let α := EuclideanSpace ℝ {w : InfinitePlace K // w.IsReal}
  let β := EuclideanSpace ℂ {w : InfinitePlace K // w.IsComplex}
  change ContinuousSMul ℝ (WithLp 2 (α × β))
  letI : ContinuousSMul ℝ α := by dsimp [α]; infer_instance
  letI : ContinuousSMul ℝ β := by dsimp [β]; infer_instance
  let hprod : ContinuousSMul ℝ (α × β) := Prod.continuousSMul
  exact ⟨by
    change Continuous (fun p : ℝ × WithLp 2 (α × β) => p.1 • p.2)
    let h : Continuous (fun p : ℝ × WithLp 2 (α × β) =>
        p.1 • p.2.ofLp) := by
      exact hprod.continuous_smul.comp
        (continuous_fst.prodMk
          ((WithLp.prod_continuous_ofLp 2 α β).comp continuous_snd))
    exact (WithLp.prod_continuous_toLp 2 α β).comp h⟩

noncomputable def normalizedRawLift (P : PrimeIdeal K) {n s : ℕ}
    (S : Code P n s) : Submodule ℤ (M n 1 (K_ℝ[K])) :=
  ZLattice.comap ℝ (embeddedRawLift P S)
    (scalarLinearMap (K := K) (liftScale P n s) n)

noncomputable def columnMatrix (x : Fin n → K_ℝ[K]) : M n 1 (K_ℝ[K]) :=
  fun i _ => x i

theorem normalizedRawLift_mem_iff (P : PrimeIdeal K) {n s : ℕ}
    (S : Code P n s) (x : M n 1 (K_ℝ[K])) :
    x ∈ normalizedRawLift P S ↔
      ∃ y ∈ rawLift P S,
        x = columnMatrix ((liftScale P n s)⁻¹ • embedVector y) := by
  constructor
  · intro hx
    change scalarLinearMap (K := K) (liftScale P n s) n x ∈
      embeddedRawLift P S at hx
    rcases hx with ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    have hscale : liftScale P n s ≠ 0 :=
      ne_of_gt (liftScale_pos P n s)
    ext i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hentry := congrArg (fun z : M n 1 (K_ℝ[K]) => z i 0) hxy
    change numberEmbedding K (y i) =
      (liftScale P n s) • x i 0 at hentry
    change x i 0 = (liftScale P n s)⁻¹ • numberEmbedding K (y i)
    rw [hentry, smul_smul]
    simp [hscale]
  · rintro ⟨y, hy, rfl⟩
    change scalarLinearMap (K := K) (liftScale P n s) n
        (columnMatrix ((liftScale P n s)⁻¹ • embedVector y)) ∈
      embeddedRawLift P S
    refine ⟨y, hy, ?_⟩
    have hscale : liftScale P n s ≠ 0 :=
      ne_of_gt (liftScale_pos P n s)
    ext i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change numberEmbedding K (y i) =
      (liftScale P n s) •
        ((liftScale P n s)⁻¹ • numberEmbedding K (y i))
    rw [smul_smul]
    simp [hscale]

/- [paper, equation `eq:def_of_L`, lines 1816--1827; derived consequence]
The scalar-normalized lift has covolume one in the manuscript-normalized
matrix measure. -/
theorem normalizedRawLift_covolume_paperMatrixMeasure
    (P : PrimeIdeal K) {n s : ℕ} (S : Code P n s)
    (hsn : s ≤ n) (hn : 0 < n) :
    ZLattice.covolume (normalizedRawLift P S)
        (paperMatrixMeasure (K := K) n 1) = 1 := by
  letI : Fintype {w : InfinitePlace K // w.IsReal} := Fintype.ofFinite _
  letI : Fintype {w : InfinitePlace K // w.IsComplex} := Fintype.ofFinite _
  letI : IsTopologicalAddGroup K_ℝ[K] := kReal_isTopologicalAddGroup (K := K)
  letI : ContinuousSMul ℝ K_ℝ[K] := kReal_continuousSMul (K := K)
  letI : IsTopologicalAddGroup (M n 1 (K_ℝ[K])) := inferInstance
  letI : ContinuousSMul ℝ (M n 1 (K_ℝ[K])) := inferInstance
  let L := embeddedRawLift P S
  let discL : DiscreteTopology L := by
    dsimp only [L]
    exact embeddedRawLift_discreteTopology P S
  letI : DiscreteTopology L := discL
  letI : @IsZLattice ℝ inferInstance (M n 1 (K_ℝ[K])) inferInstance
      inferInstance L discL := by
    dsimp only [L]
    exact @embeddedRawLift_isZLattice K _ _ P n s S
  let c : ℝ := (liftScale P n s)⁻¹
  have hc : c ≠ 0 := by
    dsimp [c]
    exact inv_ne_zero (ne_of_gt (liftScale_pos P n s))
  let f : M n 1 (K_ℝ[K]) →L[ℝ] M n 1 (K_ℝ[K]) :=
    ContinuousLinearMap.mk (c • LinearMap.id) (by
      change Continuous (fun x : M n 1 (K_ℝ[K]) => (c • LinearMap.id) x)
      simpa using
        (continuous_const_smul c :
          Continuous (fun x : M n 1 (K_ℝ[K]) => c • x)))
  have hfdet : LinearMap.det f.toLinearMap ≠ 0 := by
    change LinearMap.det (c • LinearMap.id) ≠ 0
    rw [LinearMap.det_smul, LinearMap.det_id]
    simp [hc, matrix_finrank_one (K := K) n]
  let e : M n 1 (K_ℝ[K]) ≃L[ℝ] M n 1 (K_ℝ[K]) :=
    f.toContinuousLinearEquivOfDetNeZero hfdet
  have he_apply (x : M n 1 (K_ℝ[K])) : e x = c • x := by
    change f x = c • x
    change (c • LinearMap.id) x = c • x
    simp
  have he_symm : e.symm.toLinearMap =
      scalarLinearMap (K := K) (liftScale P n s) n := by
    apply LinearMap.ext
    intro x
    apply e.injective
    change e (e.symm x) = e ((scalarLinearMap (K := K)
      (liftScale P n s) n) x)
    rw [e.apply_symm_apply, he_apply]
    change x = c • ((liftScale P n s) • x)
    rw [smul_smul]
    rw [inv_mul_cancel₀ (by
      exact ne_of_gt (liftScale_pos P n s)), one_smul]
  have hcov := @covolume_comap_symm_det
      (M n 1 (K_ℝ[K])) inferInstance inferInstance inferInstance
      (kRealMatrixMeasurableSpace (K := K))
      (kRealMatrixBorelSpace (K := K))
      L discL (by exact this)
      (paperMatrixMeasure (K := K) n 1)
      (paperMatrixMeasure_isAddHaarMeasure (K := K) n 1) e
  have hmap : ZLattice.comap ℝ L e.symm.toLinearMap =
      normalizedRawLift P S := by
    change ZLattice.comap ℝ L e.symm.toLinearMap =
      ZLattice.comap ℝ L (scalarLinearMap (K := K)
        (liftScale P n s) n)
    rw [he_symm]
  have hcov' : ZLattice.covolume (normalizedRawLift P S)
      (paperMatrixMeasure (K := K) n 1) =
      |LinearMap.det e.toLinearMap| *
        ZLattice.covolume L (paperMatrixMeasure (K := K) n 1) := by
    rw [← hmap]
    exact hcov
  have hdet : |LinearMap.det e.toLinearMap| =
      ((idealNorm P : ℝ) ^ (n - s))⁻¹ := by
    have hcpos : 0 < c := by
      dsimp [c]
      exact inv_pos.mpr (liftScale_pos P n s)
    have hedet : LinearMap.det e.toLinearMap =
        c ^ (n * degree K) := by
      change LinearMap.det f.toLinearMap = _
      change LinearMap.det (c • LinearMap.id) = _
      rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
      rw [matrix_finrank_one (K := K) n]
    rw [hedet, abs_of_pos (pow_pos hcpos _), inv_pow]
    have hpow := liftScale_pow_eq_idealNorm_pow (k := 1) P hsn hn
    simpa [c] using hpow
  rw [hcov', hdet, embeddedRawLift_covolume_paperMatrixMeasure P S]
  have hnorm : idealNorm P ≠ 0 := by
    intro hzero
    apply P.2.2
    exact Ideal.absNorm_eq_zero_iff.mp hzero
  have hnormR : (idealNorm P : ℝ) ≠ 0 := by
    exact_mod_cast hnorm
  exact inv_mul_cancel₀
    (pow_ne_zero _ hnormR)

end Katznelson
