import Katznelson.Counting.FiniteField
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.NumberTheory.NumberField.Norm

/-!
# Rank drop modulo a prime ideal

This file formalizes Lemma `le:rankdrop` of `papers/katznelson.tex`.  The first
step records the finite-dimensional linear algebra used to select a nonsingular
minor from a matrix of known rank.
-/

namespace Katznelson

open Set
open scoped BigOperators Classical NumberField

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

theorem normAtPlace_le_norm {K : Type*} [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (x : K_ℝ[K]) :
    NumberField.mixedEmbedding.normAtPlace w
      (NumberField.mixedEmbedding.euclidean.toMixed K x) ≤ ‖x‖ := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [NumberField.mixedEmbedding.normAtPlace_apply_of_isReal hw]
    change ‖x.fst ⟨w, hw⟩‖ ≤ ‖x‖
    exact (PiLp.norm_apply_le x.fst ⟨w, hw⟩).trans
      (WithLp.norm_fst_le (x := x))
  · rw [NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex hw]
    change ‖x.snd ⟨w, hw⟩‖ ≤ ‖x‖
    exact (PiLp.norm_apply_le x.snd ⟨w, hw⟩).trans
      (WithLp.norm_snd_le (x := x))

theorem norm_entry_le_frobenius
    {α : Type*} [NormedAddCommGroup α] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) α) (i : Fin n) (j : Fin m) :
    ‖A i j‖ ≤ ‖A‖ := by
  change ‖(WithLp.toLp 2 fun i => WithLp.toLp 2 fun j => A i j) i j‖ ≤
    ‖WithLp.toLp 2 fun i => WithLp.toLp 2 fun j => A i j‖
  exact (PiLp.norm_apply_le _ j).trans (PiLp.norm_apply_le _ i)

/- The paper compares a matrix's Euclidean size with the sizes of its rows.
   Our row vectors inherit the finite-product supremum norm, so the elementary
   one-sided estimate below is the normalization-safe statement available
   before a full product-norm identification. -/
theorem norm_row_le_frobenius
    {α : Type*} [NormedAddCommGroup α] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) α) (i : Fin n) :
    ‖A i‖ ≤ ‖A‖ := by
  rw [Pi.norm_def]
  change ↑(Finset.univ.sup (fun b : Fin m => ‖A i b‖₊)) ≤ ‖A‖₊
  apply_mod_cast
    (Finset.sup_le (s := (Finset.univ : Finset (Fin m))) (a := ‖A‖₊) ?_)
  intro j hj
  exact_mod_cast (norm_entry_le_frobenius A i j)

section LinearAlgebra

theorem exists_linearIndependent_subfamily_of_finrank_span_eq
    {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Finite ι] (v : ι → V) {k : ℕ}
    (hfinrank : Module.finrank F (Submodule.span F (Set.range v)) = k) :
    ∃ e : Fin k → ι, LinearIndependent F (v ∘ e) := by
  classical
  let S : Submodule F V := Submodule.span F (Set.range v)
  let vS : ι → S := fun i =>
    ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
  have hvS : Submodule.span F (Set.range vS) = ⊤ := by
    apply (Submodule.span_range_subtype_eq_top_iff S
      (fun i => Submodule.subset_span (Set.mem_range_self i))).2
    rfl
  let B : Set S :=
    (linearIndepOn_empty F id).extend (Set.empty_subset (Set.range vS))
  let b : Module.Basis B F S :=
    Module.Basis.extendLe (linearIndependent_empty F S)
      (Set.empty_subset (Set.range vS)) hvS.ge
  have hBsubset : B ⊆ Set.range vS := by
    simpa [B] using
      (linearIndepOn_empty F id).extend_subset
        (Set.empty_subset (Set.range vS))
  have hBfinite : B.Finite := (Set.finite_range vS).subset hBsubset
  let _ : Fintype B := hBfinite.fintype
  have hcard : Fintype.card B = k := by
    calc
      Fintype.card B = Module.finrank F S :=
        (Module.finrank_eq_card_basis b).symm
      _ = k := by simpa [S] using hfinrank
  let eB : Fin k ≃ B := Fintype.equivOfCardEq (by simp [hcard])
  choose source hsource using fun z : B => hBsubset z.2
  refine ⟨fun i => source (eB i), ?_⟩
  have hbLI : LinearIndependent F (fun i : Fin k => b (eB i)) :=
    b.linearIndependent.comp eB eB.injective
  have hliS : LinearIndependent F (fun i : Fin k => vS (source (eB i))) := by
    convert hbLI using 1
    funext i
    rw [hsource]
    exact (Module.Basis.extendLe_apply_self (linearIndependent_empty F S)
      (Set.empty_subset (Set.range vS)) hvS.ge (eB i)).symm
  have hliV := hliS.map' S.subtype (by simp)
  have hfun :
      S.subtype ∘ (fun i : Fin k => vS (source (eB i))) =
        v ∘ (fun i => source (eB i)) := by
    rfl
  rw [hfun] at hliV
  exact hliV

end LinearAlgebra

section Minors

theorem exists_nonsingular_minor_of_rank_eq
    {F : Type*} [Field F] {n m k : ℕ} (A : Matrix (Fin n) (Fin m) F)
    (hA : A.rank = k) :
    ∃ (rows : Fin k → Fin n) (cols : Fin k → Fin m),
      (A.submatrix rows cols).det ≠ 0 := by
  classical
  have hrowspan :
      Module.finrank F (Submodule.span F (Set.range A.row)) = k := by
    rw [← A.rank_eq_finrank_span_row, hA]
  obtain ⟨rows, hrows⟩ :=
    exists_linearIndependent_subfamily_of_finrank_span_eq A.row hrowspan
  let B : Matrix (Fin k) (Fin m) F := A.submatrix rows id
  have hBrows : LinearIndependent F B.row := by
    change LinearIndependent F (A ∘ rows)
    exact hrows
  have hBrank : B.rank = k := by
    simpa using hBrows.rank_matrix
  have hcolspan :
      Module.finrank F (Submodule.span F (Set.range B.col)) = k := by
    rw [← Matrix.rank_eq_finrank_span_cols, hBrank]
  obtain ⟨cols, hcols⟩ :=
    exists_linearIndependent_subfamily_of_finrank_span_eq B.col hcolspan
  have hminorCols :
      LinearIndependent F (A.submatrix rows cols).col := by
    have hfun : (A.submatrix rows cols).col = B.col ∘ cols := by
      funext i j
      rfl
    rw [hfun]
    exact hcols
  exact ⟨rows, cols,
    Matrix.nonsingular_iff_det_ne_zero.mp
      (Matrix.Nonsingular.of_linearIndependent_col hminorCols)⟩

end Minors

section RankDropWitness

variable {K : Type*} [Field K] [NumberField K]

/- Reduction modulo `P` cannot increase algebraic rank.  This is the rank
   stratification used before the paper separates the rank-drop terms. -/
theorem reduceMatrix_rank_le (P : PrimeIdeal K) {n m : ℕ}
    (A : IntegralMatrix K n m) :
    matrixRank (reduceMatrix P A) ≤ integralMatrixRank A := by
  classical
  obtain ⟨rows, cols, hdetP⟩ :=
    exists_nonsingular_minor_of_rank_eq (reduceMatrix P A) rfl
  have hmapP :
      RingHom.mapMatrix (Ideal.Quotient.mk P.1)
          (A.submatrix rows cols) =
        (reduceMatrix P A).submatrix rows cols := by
    ext i j
    rfl
  have hdeta : (A.submatrix rows cols).det ≠ 0 := by
    intro hzero
    apply hdetP
    rw [← hmapP, ← RingHom.map_det, hzero, map_zero]
  have hmapK :
      RingHom.mapMatrix (algebraMap (𝓞 K) K)
          (A.submatrix rows cols) =
        (algebraicMatrix A).submatrix rows cols := by
    ext i j
    rfl
  have hdetK : ((algebraicMatrix A).submatrix rows cols).det ≠ 0 := by
    rw [← hmapK, ← RingHom.map_det]
    intro hzero
    apply hdeta
    apply NumberField.RingOfIntegers.coe_injective
    simpa using hzero
  have hrankminor :
      ((algebraicMatrix A).submatrix rows cols).rank =
        matrixRank (reduceMatrix P A) := by
    simpa [matrixRank] using Matrix.rank_of_det_ne_zero hdetK
  change matrixRank (reduceMatrix P A) ≤ (algebraicMatrix A).rank
  rw [← hrankminor]
  exact Matrix.rank_submatrix_le (algebraicMatrix A) rows cols

theorem reduceMatrix_rank_eq_of_not_lt (P : PrimeIdeal K) {n m : ℕ}
    (A : IntegralMatrix K n m)
    (hnot : ¬ matrixRank (reduceMatrix P A) < integralMatrixRank A) :
    matrixRank (reduceMatrix P A) = integralMatrixRank A :=
  Nat.le_antisymm (reduceMatrix_rank_le P A) (Nat.le_of_not_gt hnot)

theorem exists_rankDrop_minor (P : PrimeIdeal K) {n m k : ℕ}
    (A : IntegralMatrix K n m)
    (hA : integralMatrixRank A = k)
    (hdrop : matrixRank (reduceMatrix P A) < k) :
    ∃ (rows : Fin k → Fin n) (cols : Fin k → Fin m),
      (A.submatrix rows cols).det ≠ 0 ∧
        (A.submatrix rows cols).det ∈ P.1 := by
  classical
  obtain ⟨rows, cols, hdetK⟩ :=
    exists_nonsingular_minor_of_rank_eq (algebraicMatrix A) hA
  let a : Matrix (Fin k) (Fin k) (𝓞 K) := A.submatrix rows cols
  have hdet : a.det ≠ 0 := by
    intro ha
    apply hdetK
    have hmatrix :
        RingHom.mapMatrix (algebraMap (𝓞 K) K) a =
          (algebraicMatrix A).submatrix rows cols := by
      ext i j
      rfl
    rw [← hmatrix, ← RingHom.map_det, ha, map_zero]
  let b : Matrix (Fin k) (Fin k) (residueField P) :=
    (reduceMatrix P A).submatrix rows cols
  have hbrank : b.rank < k :=
    (Matrix.rank_submatrix_le (reduceMatrix P A) rows cols).trans_lt hdrop
  have hbdet : b.det = 0 := by
    by_contra hbdet
    have hrank := Matrix.rank_of_det_ne_zero hbdet
    rw [Fintype.card_fin] at hrank
    exact (ne_of_lt hbrank) hrank
  have hquot : Ideal.Quotient.mk P.1 a.det = 0 := by
    have hmatrix :
        RingHom.mapMatrix (Ideal.Quotient.mk P.1) a = b := by
      ext i j
      rfl
    rw [RingHom.map_det]
    rw [hmatrix]
    exact hbdet
  exact ⟨rows, cols, hdet,
    Ideal.Quotient.eq_zero_iff_mem.mp hquot⟩

theorem normAtPlace_det_minor_le {n m k : ℕ}
    (A : IntegralMatrix K n m) (rows : Fin k → Fin n)
    (cols : Fin k → Fin m) (w : NumberField.InfinitePlace K) :
    NumberField.mixedEmbedding.normAtPlace w
        (NumberField.mixedEmbedding K ((A.submatrix rows cols).det : K)) ≤
      (k.factorial : ℝ) * ‖embedMatrix A‖ ^ k := by
  classical
  let a : Matrix (Fin k) (Fin k) (𝓞 K) := A.submatrix rows cols
  let aK : Matrix (Fin k) (Fin k) K :=
    (algebraicMatrix A).submatrix rows cols
  have hentry (i j : Fin k) : w.1 (aK i j) ≤ ‖embedMatrix A‖ := by
    calc
      w.1 (aK i j) = NumberField.mixedEmbedding.normAtPlace w
          (NumberField.mixedEmbedding K (aK i j)) := by
        rw [NumberField.mixedEmbedding.normAtPlace_apply]
        rfl
      _ = NumberField.mixedEmbedding.normAtPlace w
          (NumberField.mixedEmbedding.euclidean.toMixed K
            (embedMatrix A (rows i) (cols j))) := by
        simp [embedMatrix, numberEmbedding, aK, algebraicMatrix]
      _ ≤ ‖embedMatrix A (rows i) (cols j)‖ :=
        normAtPlace_le_norm w _
      _ ≤ ‖embedMatrix A‖ :=
        norm_entry_le_frobenius (embedMatrix A) (rows i) (cols j)
  have hdetBound := Matrix.det_le (A := aK) (abv := w.1) hentry
  have hmatrix :
      RingHom.mapMatrix (algebraMap (𝓞 K) K) a = aK := by
    ext i j
    rfl
  have hdetEq : ((a.det : 𝓞 K) : K) = aK.det := by
    calc
      ((a.det : 𝓞 K) : K) =
          (RingHom.mapMatrix (algebraMap (𝓞 K) K) a).det :=
        (RingHom.map_det (algebraMap (𝓞 K) K) a)
      _ = aK.det := congrArg Matrix.det hmatrix
  rw [NumberField.mixedEmbedding.normAtPlace_apply]
  change w.1 ((a.det : 𝓞 K) : K) ≤ _
  rw [hdetEq]
  simpa [Fintype.card_fin, nsmul_eq_mul] using hdetBound

theorem idealNorm_le_rankDrop_minor_bound (P : PrimeIdeal K) {n m k : ℕ}
    (A : IntegralMatrix K n m) (rows : Fin k → Fin n)
    (cols : Fin k → Fin m)
    (hdet : (A.submatrix rows cols).det ≠ 0)
    (hmem : (A.submatrix rows cols).det ∈ P.1) :
    (idealNorm P : ℝ) ≤
      ((k.factorial : ℝ) * ‖embedMatrix A‖ ^ k) ^ degree K := by
  let z : 𝓞 K := (A.submatrix rows cols).det
  have hnormne : Algebra.norm ℤ z ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hdet
  have hdvd : (idealNorm P : ℤ) ∣ Algebra.norm ℤ z := by
    exact Ideal.absNorm_dvd_norm_of_mem hmem
  have hnat : idealNorm P ≤ (Algebra.norm ℤ z).natAbs := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hdvd hnormne
  have hnormCast : ((Algebra.norm ℤ z).natAbs : ℝ) =
      ((|(Algebra.norm ℚ (z : K))| : ℚ) : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, Rat.cast_abs]
    congr 1
    exact_mod_cast Algebra.coe_norm_int z
  have hlower : (idealNorm P : ℝ) ≤
      NumberField.mixedEmbedding.norm
        (NumberField.mixedEmbedding K (z : K)) := by
    calc
      (idealNorm P : ℝ) ≤ ((Algebra.norm ℤ z).natAbs : ℝ) := by
        exact_mod_cast hnat
      _ = ((|(Algebra.norm ℚ (z : K))| : ℚ) : ℝ) := hnormCast
      _ = NumberField.mixedEmbedding.norm
          (NumberField.mixedEmbedding K (z : K)) :=
        (NumberField.mixedEmbedding.norm_eq_norm (z : K)).symm
  let B : ℝ := (k.factorial : ℝ) * ‖embedMatrix A‖ ^ k
  have hplace (w : NumberField.InfinitePlace K) :
      NumberField.mixedEmbedding.normAtPlace w
          (NumberField.mixedEmbedding K (z : K)) ≤ B := by
    exact normAtPlace_det_minor_le A rows cols w
  have hnormUpper : NumberField.mixedEmbedding.norm
      (NumberField.mixedEmbedding K (z : K)) ≤ B ^ degree K := by
    rw [NumberField.mixedEmbedding.norm_apply]
    calc
      ∏ w : NumberField.InfinitePlace K,
          NumberField.mixedEmbedding.normAtPlace w
              (NumberField.mixedEmbedding K (z : K)) ^ w.mult ≤
          ∏ w : NumberField.InfinitePlace K, B ^ w.mult := by
        apply Finset.prod_le_prod
        · intro w _
          exact pow_nonneg
            (NumberField.mixedEmbedding.normAtPlace_nonneg w _) _
        · intro w _
          exact pow_le_pow_left₀
            (NumberField.mixedEmbedding.normAtPlace_nonneg w _) (hplace w) _
      _ = B ^ (∑ w : NumberField.InfinitePlace K, w.mult) := by
        rw [Finset.prod_pow_eq_pow_sum]
      _ = B ^ degree K := by
        rw [NumberField.InfinitePlace.sum_mult_eq]
        rfl
  exact hlower.trans hnormUpper

/- Lemma `le:rankdrop` in the paper.  The use of `m!` makes the constant
   independent of the actual rank `k`, as required there. -/
theorem rankDrop_norm_lower_bound (P : PrimeIdeal K) {n m k : ℕ}
    (hk : 1 ≤ k) (hkm : k ≤ m) (A : IntegralMatrix K n m)
    (hA : integralMatrixRank A = k)
    (hdrop : matrixRank (reduceMatrix P A) < k) :
    (m.factorial : ℝ)⁻¹ *
        Real.rpow (idealNorm P : ℝ)
          (1 / ((k : ℝ) * (degree K : ℝ))) ≤
      ‖embedMatrix A‖ := by
  obtain ⟨rows, cols, hdet, hmem⟩ :=
    exists_rankDrop_minor P A hA hdrop
  have hq := idealNorm_le_rankDrop_minor_bound P A rows cols hdet hmem
  let c : ℝ := k.factorial
  let R : ℝ := ‖embedMatrix A‖
  let B : ℝ := c * R ^ k
  have hc : 1 ≤ c := by
    dsimp [c]
    exact_mod_cast Nat.factorial_pos k
  have hR : 0 ≤ R := by
    exact norm_nonneg _
  have hB : 0 ≤ B := mul_nonneg (zero_le_one.trans hc) (pow_nonneg hR _)
  have hBpow : B ≤ (c * R) ^ k := by
    dsimp [B]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right
      (by simpa using pow_le_pow_right₀ hc hk) (pow_nonneg hR _)
  have hdegree : 0 < degree K := by
    exact Module.finrank_pos
  have hkd : 0 < k * degree K := Nat.mul_pos hk hdegree
  have hqpow : (idealNorm P : ℝ) ≤ (c * R) ^ (k * degree K) := by
    calc
      (idealNorm P : ℝ) ≤ B ^ degree K := by simpa [B, c, R] using hq
      _ ≤ ((c * R) ^ k) ^ degree K :=
        pow_le_pow_left₀ hB hBpow _
      _ = (c * R) ^ (k * degree K) := by rw [pow_mul]
  have hroot :
      Real.rpow (idealNorm P : ℝ)
          (((k * degree K : ℕ) : ℝ)⁻¹) ≤ c * R := by
    apply (Real.rpow_inv_le_iff_of_pos
      (by positivity) (mul_nonneg (zero_le_one.trans hc) hR)
      (by exact_mod_cast hkd)).2
    simpa only [← Nat.cast_mul, Real.rpow_natCast] using hqpow
  have hfactorial : c ≤ (m.factorial : ℝ) := by
    dsimp [c]
    exact_mod_cast Nat.factorial_le hkm
  have hroot' :
      Real.rpow (idealNorm P : ℝ)
          (((k * degree K : ℕ) : ℝ)⁻¹) ≤
        (m.factorial : ℝ) * R :=
    hroot.trans (mul_le_mul_of_nonneg_right hfactorial hR)
  have hexponent :
      1 / ((k : ℝ) * (degree K : ℝ)) =
        (((k * degree K : ℕ) : ℝ)⁻¹) := by
    rw [one_div, Nat.cast_mul]
  rw [hexponent]
  calc
    (m.factorial : ℝ)⁻¹ *
        Real.rpow (idealNorm P : ℝ)
          (((k * degree K : ℕ) : ℝ)⁻¹) ≤
        (m.factorial : ℝ)⁻¹ * ((m.factorial : ℝ) * R) :=
      mul_le_mul_of_nonneg_left hroot' (by positivity)
    _ = R := by
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    _ = ‖embedMatrix A‖ := rfl

end RankDropWitness

end Katznelson
