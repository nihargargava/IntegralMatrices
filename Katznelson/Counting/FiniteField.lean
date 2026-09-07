import Katznelson.Lifts
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Finite-field code counting

This file begins the formalization of Lemma `le:counting` in
`papers/katznelson.tex` (arXiv:2510.11673).  The paper averages over all
`s`-dimensional subspaces of `k_𝓟^n`; here those subspaces are the finite type
`Code P n s`.
-/

namespace Katznelson

open Set
open scoped BigOperators NumberField

section

variable {K : Type*} [Field K] [NumberField K]

/- The normalized product occurring in the Gaussian-binomial formula. -/
noncomputable def gaussianProduct (q : ℝ) (t u : ℕ) : ℝ :=
  ∏ i : Fin u, (1 - q ^ i.val / q ^ t)

noncomputable def gaussianCorrection (q : ℝ) (t u : ℕ) : ℝ :=
  gaussianProduct q t u / gaussianProduct q u u

theorem card_residueField_eq_idealNorm (P : PrimeIdeal K) :
    Fintype.card (residueField P) = idealNorm P := by
  rw [idealNorm, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_eq_fintype_card]

theorem prod_pow_sub_pow_eq (q : ℝ) {t u : ℕ} (hq : q ≠ 0) :
    ∏ i : Fin u, (q ^ t - q ^ i.val) =
      q ^ (t * u) * gaussianProduct q t u := by
  rw [gaussianProduct]
  calc
    ∏ i : Fin u, (q ^ t - q ^ i.val) =
        ∏ i : Fin u, q ^ t * (1 - q ^ i.val / q ^ t) := by
      apply Finset.prod_congr rfl
      intro i _
      field_simp [pow_ne_zero t hq]
    _ = (∏ _i : Fin u, q ^ t) *
        ∏ i : Fin u, (1 - q ^ i.val / q ^ t) :=
      Finset.prod_mul_distrib
    _ = q ^ (t * u) *
        ∏ i : Fin u, (1 - q ^ i.val / q ^ t) := by
      rw [Fin.prod_const, pow_mul]

theorem natCast_prod_pow_sub_pow (q t u : ℕ) (hq : 1 ≤ q)
    (hut : u ≤ t) :
    ((∏ i : Fin u, (q ^ t - q ^ i.val) : ℕ) : ℝ) =
      ∏ i : Fin u, ((q : ℝ) ^ t - (q : ℝ) ^ i.val) := by
  rw [Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [Nat.cast_sub]
  · norm_cast
  · exact pow_le_pow_right' hq (i.isLt.le.trans hut)

theorem pow_div_pow_le_inv (q : ℝ) {i t : ℕ} (hq : 1 ≤ q)
    (hqpos : 0 < q) (hit : i < t) :
    0 ≤ q ^ i / q ^ t ∧ q ^ i / q ^ t ≤ q⁻¹ := by
  constructor
  · positivity
  · rw [show q⁻¹ = 1 / q by simp,
      div_le_div_iff₀ (pow_pos hqpos t) hqpos]
    simpa [pow_succ] using
      (pow_le_pow_right₀ hq (Nat.succ_le_of_lt hit))

theorem one_sub_gaussianProduct_le (q : ℝ) {t u : ℕ}
    (hq : 2 ≤ q) (hut : u ≤ t) :
    0 ≤ 1 - gaussianProduct q t u ∧
      1 - gaussianProduct q t u ≤ (u : ℝ) / q := by
  have hqpos : 0 < q := by linarith
  have hqone : 1 ≤ q := by linarith
  have hratio (i : Fin u) :
      0 ≤ q ^ i.val / q ^ t ∧ q ^ i.val / q ^ t ≤ q⁻¹ :=
    pow_div_pow_le_inv q hqone hqpos (i.isLt.trans_le hut)
  have hratio_one (i : Fin u) : q ^ i.val / q ^ t ≤ 1 :=
    (hratio i).2.trans ((inv_le_one₀ hqpos).2 hqone)
  have hprod_nonneg : 0 ≤ gaussianProduct q t u := by
    exact Finset.prod_nonneg fun i _ => sub_nonneg.mpr (hratio_one i)
  have hprod_le_one : gaussianProduct q t u ≤ 1 := by
    exact Finset.prod_le_one
      (fun i _ => sub_nonneg.mpr (hratio_one i))
      (fun i _ => by linarith [(hratio i).1])
  constructor
  · linarith
  · rw [gaussianProduct, Finset.prod_one_sub_ordered]
    simp only [sub_sub_cancel]
    calc
      ∑ i : Fin u, q ^ i.val / q ^ t *
          ∏ j ∈ Finset.univ with j < i, (1 - q ^ j.val / q ^ t) ≤
          ∑ _i : Fin u, q⁻¹ := by
        apply Finset.sum_le_sum
        intro i _
        have hpartial_nonneg :
            0 ≤ ∏ j ∈ Finset.univ with j < i, (1 - q ^ j.val / q ^ t) := by
          exact Finset.prod_nonneg fun j hj =>
            sub_nonneg.mpr (hratio_one j)
        have hpartial_le :
            ∏ j ∈ Finset.univ with j < i, (1 - q ^ j.val / q ^ t) ≤ 1 := by
          exact Finset.prod_le_one
            (fun j hj => sub_nonneg.mpr (hratio_one j))
            (fun j hj => by linarith [(hratio j).1])
        exact (mul_le_of_le_one_right (hratio i).1 hpartial_le).trans
          (hratio i).2
      _ = (u : ℝ) / q := by
        simp [div_eq_mul_inv]

theorem gaussianProduct_lower_bound (q : ℝ) {t u : ℕ}
    (hq : 2 ≤ q) (hut : u ≤ t) :
    (2 : ℝ)⁻¹ ^ u ≤ gaussianProduct q t u := by
  have hqpos : 0 < q := by linarith
  have hqone : 1 ≤ q := by linarith
  have hratio (i : Fin u) : q ^ i.val / q ^ t ≤ q⁻¹ :=
    (pow_div_pow_le_inv q hqone hqpos (i.isLt.trans_le hut)).2
  have hinv : q⁻¹ ≤ (2 : ℝ)⁻¹ := by
    exact (inv_le_inv₀ hqpos (show 0 < (2 : ℝ) by norm_num)).2 hq
  rw [← Fin.prod_const]
  rw [gaussianProduct]
  exact Finset.prod_le_prod
    (fun _ _ => by positivity)
    (fun i _ => by linarith [hratio i, hinv])

theorem gaussianCorrection_error_bound (q : ℝ) {t u : ℕ}
    (hq : 2 ≤ q) (hut : u ≤ t) :
    |gaussianCorrection q t u - 1| ≤
      ((u : ℝ) * 2 ^ u) / q := by
  have hqpos : 0 < q := by linarith
  have htu := one_sub_gaussianProduct_le q hq hut
  have huu := one_sub_gaussianProduct_le q hq (le_refl u)
  have hlower := gaussianProduct_lower_bound q hq (le_refl u)
  have hcpos : 0 < (2 : ℝ)⁻¹ ^ u := by positivity
  have hdenompos : 0 < gaussianProduct q u u := hcpos.trans_le hlower
  have hdiff :
      |gaussianProduct q t u - gaussianProduct q u u| ≤ (u : ℝ) / q := by
    rw [abs_le]
    constructor <;> linarith
  have huq : 0 ≤ (u : ℝ) / q := by positivity
  have hquot : gaussianCorrection q t u - 1 =
      (gaussianProduct q t u - gaussianProduct q u u) /
        gaussianProduct q u u := by
    rw [gaussianCorrection]
    field_simp [ne_of_gt hdenompos]
  rw [hquot, abs_div, abs_of_pos hdenompos]
  calc
    |gaussianProduct q t u - gaussianProduct q u u| /
        gaussianProduct q u u ≤
        ((u : ℝ) / q) / gaussianProduct q u u :=
      div_le_div₀ huq hdiff hdenompos le_rfl
    _ ≤ ((u : ℝ) / q) / ((2 : ℝ)⁻¹ ^ u) :=
      div_le_div_of_nonneg_left huq hcpos hlower
    _ = ((u : ℝ) * 2 ^ u) / q := by
      simp [div_eq_mul_inv]
      ring

theorem gaussianCorrection_lower_bound (q : ℝ) {t u : ℕ}
    (hq : 2 ≤ q) (hut : u ≤ t) :
    (2 : ℝ)⁻¹ ^ u ≤ gaussianCorrection q t u := by
  have hdenomBounds := one_sub_gaussianProduct_le q hq (le_refl u)
  have hdenomPos : 0 < gaussianProduct q u u :=
    (show 0 < (2 : ℝ)⁻¹ ^ u by positivity).trans_le
      (gaussianProduct_lower_bound q hq (le_refl u))
  rw [gaussianCorrection, le_div_iff₀ hdenomPos]
  calc
    (2 : ℝ)⁻¹ ^ u * gaussianProduct q u u ≤
        (2 : ℝ)⁻¹ ^ u * 1 := by
      apply mul_le_mul_of_nonneg_left
      · linarith [hdenomBounds.1]
      · positivity
    _ = (2 : ℝ)⁻¹ ^ u := mul_one _
    _ ≤ gaussianProduct q t u := gaussianProduct_lower_bound q hq hut

theorem gaussianCorrection_quotient_error_bound (q : ℝ)
    {t₁ u₁ t₂ u₂ : ℕ} (hq : 2 ≤ q)
    (hu₁ : u₁ ≤ t₁) (hu₂ : u₂ ≤ t₂) :
    |gaussianCorrection q t₁ u₁ / gaussianCorrection q t₂ u₂ - 1| ≤
      (((u₁ : ℝ) * 2 ^ u₁ + (u₂ : ℝ) * 2 ^ u₂) * 2 ^ u₂) / q := by
  let a := gaussianCorrection q t₁ u₁
  let b := gaussianCorrection q t₂ u₂
  have hqpos : 0 < q := by linarith
  have ha := gaussianCorrection_error_bound q hq hu₁
  have hb := gaussianCorrection_error_bound q hq hu₂
  have hbLower := gaussianCorrection_lower_bound q hq hu₂
  have hcpos : 0 < (2 : ℝ)⁻¹ ^ u₂ := by positivity
  have hbpos : 0 < b := hcpos.trans_le hbLower
  have hab : |a - b| ≤
      ((u₁ : ℝ) * 2 ^ u₁ + (u₂ : ℝ) * 2 ^ u₂) / q := by
    calc
      |a - b| ≤ |a - 1| + |1 - b| := abs_sub_le a 1 b
      _ = |a - 1| + |b - 1| := by rw [abs_sub_comm 1 b]
      _ ≤ ((u₁ : ℝ) * 2 ^ u₁) / q +
          ((u₂ : ℝ) * 2 ^ u₂) / q := add_le_add ha hb
      _ = ((u₁ : ℝ) * 2 ^ u₁ + (u₂ : ℝ) * 2 ^ u₂) / q := by ring
  have hconst : 0 ≤
      ((u₁ : ℝ) * 2 ^ u₁ + (u₂ : ℝ) * 2 ^ u₂) / q := by positivity
  have hquot : a / b - 1 = (a - b) / b := by
    field_simp [ne_of_gt hbpos]
  change |a / b - 1| ≤ _
  rw [hquot, abs_div, abs_of_pos hbpos]
  calc
    |a - b| / b ≤
        (((u₁ : ℝ) * 2 ^ u₁ + (u₂ : ℝ) * 2 ^ u₂) / q) / b :=
      div_le_div₀ hconst hab hbpos le_rfl
    _ ≤ (((u₁ : ℝ) * 2 ^ u₁ + (u₂ : ℝ) * 2 ^ u₂) / q) /
        ((2 : ℝ)⁻¹ ^ u₂) :=
      div_le_div_of_nonneg_left hconst hcpos hbLower
    _ = (((u₁ : ℝ) * 2 ^ u₁ + (u₂ : ℝ) * 2 ^ u₂) * 2 ^ u₂) / q := by
      simp [div_eq_mul_inv]
      ring

/- A fixed span of residue vectors. -/
def codeSpan (P : PrimeIdeal K) {n k : ℕ}
    (y : Fin k → (Fin n → residueField P)) : Submodule (residueField P)
      (Fin n → residueField P) :=
  Submodule.span (residueField P) (Set.range y)

/- The matrix obtained by reducing every entry modulo `𝓟`. -/
def reduceMatrix (P : PrimeIdeal K) {n m : ℕ}
    (A : IntegralMatrix K n m) : M n m (residueField P) :=
  fun i j => Ideal.Quotient.mk P.1 (A i j)

/- The columns of the reduced matrix, written as vectors in `k_𝓟^n`. -/
def residueColumns (P : PrimeIdeal K) {n m : ℕ}
    (A : IntegralMatrix K n m) : Fin m → (Fin n → residueField P) :=
  fun j => fun i => Ideal.Quotient.mk P.1 (A i j)

@[simp] theorem reduceMatrix_apply (P : PrimeIdeal K) {n m : ℕ}
    (A : IntegralMatrix K n m) (i : Fin n) (j : Fin m) :
    reduceMatrix P A i j = Ideal.Quotient.mk P.1 (A i j) := rfl

theorem reduceMatrix_col (P : PrimeIdeal K) {n m : ℕ}
    (A : IntegralMatrix K n m) (j : Fin m) :
    (reduceMatrix P A).col j = residueColumns P A j := by
  rfl

/- The matrix-level lift condition is exactly containment of the span of its
   reduced columns.  This is the bridge from the lattice average to the
   finite-field containment probability in Lemma `le:counting`. -/
theorem mem_matricesInLift_iff_codeSpan_le (P : PrimeIdeal K)
    {n m s : ℕ} (S : Code P n s) (A : IntegralMatrix K n m) :
    A ∈ matricesInLift P S ↔ codeSpan P (residueColumns P A) ≤ S.1 := by
  rw [mem_matricesInLift_iff]
  constructor
  · intro h
    rw [codeSpan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (mem_rawLift_iff P S (fun i => A i j)).1 (h j)
  · intro h j
    apply (mem_rawLift_iff P S (fun i => A i j)).2
    exact h (Submodule.subset_span (Set.mem_range_self j))

theorem reduceMatrix_rank_eq_span_finrank (P : PrimeIdeal K) {n m : ℕ}
    (A : IntegralMatrix K n m) :
    matrixRank (reduceMatrix P A) =
      Module.finrank (residueField P) (codeSpan P (residueColumns P A)) := by
  change (reduceMatrix P A).rank = _
  rw [Matrix.rank_eq_finrank_span_cols]
  rfl

theorem finrank_codeSpan_of_linearIndependent (P : PrimeIdeal K) {n k : ℕ}
    (y : Fin k → (Fin n → residueField P))
    (hy : LinearIndependent (residueField P) y) :
    Module.finrank (residueField P) (codeSpan P y) = k := by
  change Module.finrank (residueField P)
    (Submodule.span (residueField P) (Set.range y)) = k
  simpa using finrank_span_eq_card hy

/- The paper's Gaussian-binomial count is obtained by counting ordered bases.
   These are the two basis counts used in that argument. -/
theorem card_independent_residue_vectors (P : PrimeIdeal K) {n k : ℕ}
    (hk : k ≤ n) :
    Nat.card {y : Fin k → (Fin n → residueField P) //
        LinearIndependent (residueField P) y} =
      ∏ i : Fin k,
        ((Fintype.card (residueField P)) ^ n -
          (Fintype.card (residueField P)) ^ i.val) := by
  have hk' : k ≤ Module.finrank (residueField P) (Fin n → residueField P) := by
    simpa using hk
  simpa using
    (card_linearIndependent (K := residueField P) (V := Fin n → residueField P)
      (k := k) hk')

theorem card_independent_vectors_in_code (P : PrimeIdeal K) {n s : ℕ}
    (S : Code P n s) :
    Nat.card {y : Fin s → S.1 // LinearIndependent (residueField P) y} =
      ∏ i : Fin s,
        ((Fintype.card (residueField P)) ^ s -
          (Fintype.card (residueField P)) ^ i.val) := by
  have hs : s ≤ Module.finrank (residueField P) S.1 := by
    rw [S.2]
  simpa [S.2] using
    (card_linearIndependent (K := residueField P) (V := S.1) (k := s) hs)

/- Independent `s`-tuples in the ambient space, and ordered bases of one
   `s`-dimensional code.  Separating these types makes the double-counting
   argument below explicit. -/
abbrev IndependentResidueVectors (P : PrimeIdeal K) (n s : ℕ) :=
  {y : Fin s → (Fin n → residueField P) //
    LinearIndependent (residueField P) y}

abbrev OrderedCodeBasis (P : PrimeIdeal K) {n s : ℕ} (S : Code P n s) :=
  {y : Fin s → S.1 // LinearIndependent (residueField P) y}

def spanCode (P : PrimeIdeal K) {n s : ℕ}
    (y : IndependentResidueVectors P n s) : Code P n s :=
  ⟨codeSpan P y.1, by
    change Module.finrank (residueField P)
      (Submodule.span (residueField P) (Set.range y.1)) = s
    simpa using finrank_span_eq_card y.2⟩

theorem span_coe_orderedCodeBasis (P : PrimeIdeal K) {n s : ℕ}
    (S : Code P n s) (y : OrderedCodeBasis P S) :
    codeSpan P (fun i => (y.1 i : Fin n → residueField P)) = S.1 := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [codeSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (y.1 i).2
  · have hy : LinearIndependent (residueField P)
        (fun i => (y.1 i : Fin n → residueField P)) := by
      simpa [Function.comp_def] using
        y.2.map' S.1.subtype (by simp)
    calc
      Module.finrank (residueField P)
          (codeSpan P (fun i => (y.1 i : Fin n → residueField P))) = s := by
        change Module.finrank (residueField P)
          (Submodule.span (residueField P)
            (Set.range (fun i => (y.1 i : Fin n → residueField P)))) = s
        simpa using finrank_span_eq_card hy
      _ = Module.finrank (residueField P) S.1 := S.2.symm

def spanCodeFiberEquivOrderedCodeBasis (P : PrimeIdeal K) {n s : ℕ}
    (S : Code P n s) :
    {y : IndependentResidueVectors P n s // spanCode P y = S} ≃
      OrderedCodeBasis P S where
  toFun y :=
    ⟨fun i =>
      ⟨y.1.1 i, by
        have hspan : codeSpan P y.1.1 = S.1 :=
          congrArg Subtype.val y.2
        rw [← hspan]
        exact Submodule.subset_span (Set.mem_range_self i)⟩,
      by
        apply LinearIndependent.of_comp S.1.subtype
        simpa [Function.comp_def] using y.1.2⟩
  invFun y :=
    ⟨⟨fun i => (y.1 i : Fin n → residueField P), by
        simpa [Function.comp_def] using
          y.2.map' S.1.subtype (by simp)⟩,
      by
        apply Subtype.ext
        exact span_coe_orderedCodeBasis P S y⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    rfl
  right_inv y := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rfl

theorem card_spanCode_fiber (P : PrimeIdeal K) {n s : ℕ}
    (S : Code P n s) :
    Nat.card {y : IndependentResidueVectors P n s // spanCode P y = S} =
      ∏ i : Fin s,
        ((Fintype.card (residueField P)) ^ s -
          (Fintype.card (residueField P)) ^ i.val) := by
  calc
    Nat.card {y : IndependentResidueVectors P n s // spanCode P y = S} =
        Nat.card (OrderedCodeBasis P S) :=
      Nat.card_congr (spanCodeFiberEquivOrderedCodeBasis P S)
    _ = ∏ i : Fin s,
          ((Fintype.card (residueField P)) ^ s -
            (Fintype.card (residueField P)) ^ i.val) :=
      card_independent_vectors_in_code P S

theorem card_code_mul_orderedBasis (P : PrimeIdeal K) {n s : ℕ}
    (hs : s ≤ n) :
    Fintype.card (Code P n s) *
        (∏ i : Fin s,
          ((Fintype.card (residueField P)) ^ s -
            (Fintype.card (residueField P)) ^ i.val)) =
      ∏ i : Fin s,
        ((Fintype.card (residueField P)) ^ n -
          (Fintype.card (residueField P)) ^ i.val) := by
  let q := Fintype.card (residueField P)
  let B := ∏ i : Fin s, (q ^ s - q ^ i.val)
  have hdecomp :
      Nat.card (IndependentResidueVectors P n s) =
        ∑ S : Code P n s,
          Nat.card {y : IndependentResidueVectors P n s // spanCode P y = S} := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr
      (Equiv.sigmaFiberEquiv (spanCode P : IndependentResidueVectors P n s → Code P n s)).symm
  have hambient : Nat.card (IndependentResidueVectors P n s) =
      ∏ i : Fin s, (q ^ n - q ^ i.val) := by
    simpa [q] using card_independent_residue_vectors P hs
  have hfiber (S : Code P n s) :
      Nat.card {y : IndependentResidueVectors P n s // spanCode P y = S} = B := by
    simpa [q, B] using card_spanCode_fiber P S
  rw [hdecomp] at hambient
  simpa [q, B, hfiber, mul_comm] using hambient

theorem card_code_eq_gaussian (P : PrimeIdeal K) {n s : ℕ}
    (hs : s ≤ n) :
    (Fintype.card (Code P n s) : ℝ) =
      (Fintype.card (residueField P) : ℝ) ^ (s * (n - s)) *
        gaussianCorrection (Fintype.card (residueField P) : ℝ) n s := by
  let qNat := Fintype.card (residueField P)
  let q : ℝ := qNat
  have hqNat : 1 < qNat := Fintype.one_lt_card
  have hqOne : 1 ≤ qNat := hqNat.le
  have hqPos : 0 < q := by
    change (0 : ℝ) < (qNat : ℝ)
    exact_mod_cast (lt_trans Nat.zero_lt_one hqNat)
  have hq : q ≠ 0 := by
    exact ne_of_gt hqPos
  have hcountNat := card_code_mul_orderedBasis P hs
  have hcount := congrArg (fun z : ℕ => (z : ℝ)) hcountNat
  rw [Nat.cast_mul,
    natCast_prod_pow_sub_pow qNat s s hqOne le_rfl,
    natCast_prod_pow_sub_pow qNat n s hqOne hs,
    prod_pow_sub_pow_eq q hq, prod_pow_sub_pow_eq q hq] at hcount
  have hdenom : gaussianProduct q s s ≠ 0 := by
    have hqTwoNat : 2 ≤ qNat := by omega
    have hqReal : (2 : ℝ) ≤ q := by
      change (2 : ℝ) ≤ (qNat : ℝ)
      exact_mod_cast hqTwoNat
    exact ne_of_gt ((show 0 < (2 : ℝ)⁻¹ ^ s by positivity).trans_le
      (gaussianProduct_lower_bound q hqReal le_rfl))
  have hpow : q ^ (s * s) ≠ 0 := pow_ne_zero _ hq
  have hcanc :
      (Fintype.card (Code P n s) : ℝ) * gaussianProduct q s s =
        q ^ (s * (n - s)) * gaussianProduct q n s := by
    apply (mul_left_cancel₀ hpow)
    calc
      q ^ (s * s) *
          ((Fintype.card (Code P n s) : ℝ) * gaussianProduct q s s) =
          (Fintype.card (Code P n s) : ℝ) *
            (q ^ (s * s) * gaussianProduct q s s) := by ring
      _ = q ^ (n * s) * gaussianProduct q n s := hcount
      _ = q ^ (s * s) *
          (q ^ (s * (n - s)) * gaussianProduct q n s) := by
        have hexp : n * s = s * s + s * (n - s) := by
          calc
            n * s = (s + (n - s)) * s := by rw [Nat.add_sub_of_le hs]
            _ = s * s + s * (n - s) := by ring
        rw [hexp, pow_add]
        ring
  change (Fintype.card (Code P n s) : ℝ) =
    q ^ (s * (n - s)) * gaussianCorrection q n s
  rw [gaussianCorrection, ← mul_div_assoc, eq_div_iff hdenom]
  exact hcanc

theorem two_le_idealNorm (P : PrimeIdeal K) : 2 ≤ idealNorm P := by
  rw [← card_residueField_eq_idealNorm P]
  exact Fintype.one_lt_card

theorem two_le_idealNorm_real (P : PrimeIdeal K) :
    (2 : ℝ) ≤ (idealNorm P : ℝ) := by
  exact_mod_cast two_le_idealNorm P

theorem card_code_eq_gaussian_norm (P : PrimeIdeal K) {n s : ℕ}
    (hs : s ≤ n) :
    (Fintype.card (Code P n s) : ℝ) =
      (idealNorm P : ℝ) ^ (s * (n - s)) *
        gaussianCorrection (idealNorm P : ℝ) n s := by
  simpa only [card_residueField_eq_idealNorm P] using
    card_code_eq_gaussian P hs

/- The correspondence theorem for subspaces is dimension preserving up to
   subtracting the dimension of the quotient kernel. -/
theorem finrank_map_mkQ_of_le
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (W S : Submodule F V) (hWS : W ≤ S) :
    Module.finrank F (S.map W.mkQ) =
      Module.finrank F S - Module.finrank F W := by
  let f : S →ₗ[F] V ⧸ W := W.mkQ.domRestrict S
  have hker : LinearMap.ker f = W.comap S.subtype := by
    ext x
    simp [f]
  calc
    Module.finrank F (S.map W.mkQ) =
        Module.finrank F (LinearMap.range f) := by
      rw [LinearMap.range_domRestrict]
    _ = Module.finrank F (S ⧸ LinearMap.ker f) :=
      (LinearEquiv.finrank_eq f.quotKerEquivRange).symm
    _ = Module.finrank F S - Module.finrank F (LinearMap.ker f) :=
      Submodule.finrank_quotient _
    _ = Module.finrank F S - Module.finrank F W := by
      rw [hker, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hWS)]

theorem finrank_comap_mkQ
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (W : Submodule F V)
    (Q : Submodule F (V ⧸ W)) :
    Module.finrank F (Q.comap W.mkQ) =
      Module.finrank F Q + Module.finrank F W := by
  have hWS : W ≤ Q.comap W.mkQ := Submodule.le_comap_mkQ W Q
  have hmap : (Q.comap W.mkQ).map W.mkQ = Q := by
    exact Submodule.map_comap_eq_self (by simp)
  have hdim := finrank_map_mkQ_of_le W (Q.comap W.mkQ) hWS
  rw [hmap] at hdim
  have hle : Module.finrank F W ≤ Module.finrank F (Q.comap W.mkQ) :=
    Submodule.finrank_mono hWS
  omega

/- Fixed-dimensional subspaces are transported by a linear equivalence. -/
def fixedDimSubspaceEquiv
    {F V V' : Type*} [Field F]
    [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']
    (e : V ≃ₗ[F] V') (s : ℕ) :
    {S : Submodule F V // Module.finrank F S = s} ≃
      {S : Submodule F V' // Module.finrank F S = s} where
  toFun S :=
    ⟨S.1.map (e : V →ₗ[F] V'), by
      rw [← LinearEquiv.finrank_eq (e.submoduleMap S.1)]
      exact S.2⟩
  invFun S :=
    ⟨S.1.map (e.symm : V' →ₗ[F] V), by
      rw [← LinearEquiv.finrank_eq (e.symm.submoduleMap S.1)]
      exact S.2⟩
  left_inv S := by
    apply Subtype.ext
    change (S.1.map (e : V →ₗ[F] V')).map (e.symm : V' →ₗ[F] V) = S.1
    rw [← Submodule.map_comp, e.symm_comp, Submodule.map_id]
  right_inv S := by
    apply Subtype.ext
    change (S.1.map (e.symm : V' →ₗ[F] V)).map (e : V →ₗ[F] V') = S.1
    rw [← Submodule.map_comp, e.comp_symm, Submodule.map_id]

abbrev QuotientCode (P : PrimeIdeal K) {n : ℕ}
    (W : Submodule (residueField P) (Fin n → residueField P)) (u : ℕ) :=
  {Q : Submodule (residueField P)
      ((Fin n → residueField P) ⧸ W) //
    Module.finrank (residueField P) Q = u}

noncomputable instance quotientCode.finite (P : PrimeIdeal K) {n : ℕ}
    (W : Submodule (residueField P) (Fin n → residueField P)) (u : ℕ) :
    Finite (QuotientCode P W u) := by
  infer_instance

noncomputable instance quotientCode.fintype (P : PrimeIdeal K) {n : ℕ}
    (W : Submodule (residueField P) (Fin n → residueField P)) (u : ℕ) :
    Fintype (QuotientCode P W u) := Fintype.ofFinite _

noncomputable def quotientCodeEquivCode (P : PrimeIdeal K) {n k u : ℕ}
    (W : Submodule (residueField P) (Fin n → residueField P))
    (hW : Module.finrank (residueField P) W = k) :
    QuotientCode P W u ≃ Code P (n - k) u := by
  let e : ((Fin n → residueField P) ⧸ W) ≃ₗ[residueField P]
      (Fin (n - k) → residueField P) :=
    LinearEquiv.ofFinrankEq ((Fin n → residueField P) ⧸ W)
      (Fin (n - k) → residueField P) (by
      rw [Submodule.finrank_quotient, hW]
      simp)
  exact fixedDimSubspaceEquiv e u

abbrev ContainingCode (P : PrimeIdeal K) {n s k : ℕ}
    (y : Fin k → (Fin n → residueField P)) :=
  {S : Code P n s // codeSpan P y ≤ S.1}

noncomputable instance containingCode.finite (P : PrimeIdeal K) {n s k : ℕ}
    (y : Fin k → (Fin n → residueField P)) :
    Finite (ContainingCode P (s := s) y) := by
  infer_instance

noncomputable instance containingCode.fintype (P : PrimeIdeal K) {n s k : ℕ}
    (y : Fin k → (Fin n → residueField P)) :
    Fintype (ContainingCode P (s := s) y) := Fintype.ofFinite _

def containingCodeEquivQuotientCode (P : PrimeIdeal K) {n s k : ℕ}
    (y : Fin k → (Fin n → residueField P))
    (hy : LinearIndependent (residueField P) y) (hks : k ≤ s) :
    ContainingCode P (s := s) y ≃ QuotientCode P (codeSpan P y) (s - k) where
  toFun S :=
    ⟨S.1.1.map (codeSpan P y).mkQ, by
      rw [finrank_map_mkQ_of_le (codeSpan P y) S.1.1 S.2,
        S.1.2, finrank_codeSpan_of_linearIndependent P y hy]⟩
  invFun Q :=
    ⟨⟨Q.1.comap (codeSpan P y).mkQ, by
        rw [finrank_comap_mkQ, Q.2,
          finrank_codeSpan_of_linearIndependent P y hy,
          Nat.sub_add_cancel hks]⟩,
      Submodule.le_comap_mkQ (codeSpan P y) Q.1⟩
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    change (S.1.1.map (codeSpan P y).mkQ).comap (codeSpan P y).mkQ = S.1.1
    rw [Submodule.comap_map_mkQ, sup_eq_right]
    exact S.2
  right_inv Q := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by simp)

/- The codes counted in the numerator of the probability in `le:counting`. -/
noncomputable def containingCodes (P : PrimeIdeal K) {n s k : ℕ}
    (y : Fin k → (Fin n → residueField P)) : Finset (Code P n s) := by
  classical
  exact Finset.univ.filter fun S => codeSpan P y ≤ S.1

theorem card_containingCodes (P : PrimeIdeal K) {n s k : ℕ}
    (y : Fin k → (Fin n → residueField P))
    (hy : LinearIndependent (residueField P) y) (hks : k ≤ s) :
    (containingCodes P (n := n) (s := s) y).card =
      Fintype.card (Code P (n - k) (s - k)) := by
  classical
  calc
    (containingCodes P (n := n) (s := s) y).card =
        Fintype.card (ContainingCode P (s := s) y) := by
      rw [containingCodes]
      exact (Fintype.card_subtype
        (fun S : Code P n s => codeSpan P y ≤ S.1)).symm
    _ = Fintype.card (QuotientCode P (codeSpan P y) (s - k)) :=
      Fintype.card_congr (containingCodeEquivQuotientCode P y hy hks)
    _ = Fintype.card (Code P (n - k) (s - k)) :=
      Fintype.card_congr
        (quotientCodeEquivCode P (codeSpan P y)
          (finrank_codeSpan_of_linearIndependent P y hy))

/- The normalized count of codes containing the prescribed span. -/
noncomputable def codeContainmentProbability (P : PrimeIdeal K)
    (n s k : ℕ) (y : Fin k → (Fin n → residueField P)) : ℝ :=
  (containingCodes P (n := n) (s := s) (k := k) y).card /
    (Fintype.card (Code P n s) : ℝ)

theorem mem_containingCodes_iff (P : PrimeIdeal K) {n s k : ℕ}
    (y : Fin k → (Fin n → residueField P)) (S : Code P n s) :
    S ∈ containingCodes P y ↔ codeSpan P y ≤ S.1 := by
  simp [containingCodes]

/- The factor multiplying the leading power of `𝓝(P)` in Lemma
   `le:counting`.  Its distance from one is uniform in `P`. -/
noncomputable def codeContainmentCorrection (P : PrimeIdeal K)
    (n s k : ℕ) : ℝ :=
  gaussianCorrection (idealNorm P : ℝ) (n - k) (s - k) /
    gaussianCorrection (idealNorm P : ℝ) n s

noncomputable def codeContainmentError (P : PrimeIdeal K)
    (n s k : ℕ) : ℝ :=
  codeContainmentCorrection P n s k - 1

@[simp]
theorem codeContainmentCorrection_zero (P : PrimeIdeal K) (n s : ℕ)
    (hsn : s ≤ n) :
    codeContainmentCorrection P n s 0 = 1 := by
  rw [codeContainmentCorrection]
  exact div_self ((show 0 < (2 : ℝ)⁻¹ ^ s by positivity).trans_le
    (gaussianCorrection_lower_bound
      (idealNorm P : ℝ) (two_le_idealNorm_real P) hsn)).ne'

@[simp]
theorem codeContainmentError_zero (P : PrimeIdeal K) (n s : ℕ)
    (hsn : s ≤ n) :
    codeContainmentError P n s 0 = 0 := by
  simp [codeContainmentError, codeContainmentCorrection_zero P n s hsn]

theorem codeContainmentProbability_eq (P : PrimeIdeal K)
    {n s k : ℕ} (y : Fin k → (Fin n → residueField P))
    (hy : LinearIndependent (residueField P) y)
    (hks : k ≤ s) (hsn : s ≤ n) :
    codeContainmentProbability P n s k y =
      ((idealNorm P : ℝ) ^ (k * (n - s)))⁻¹ *
        codeContainmentCorrection P n s k := by
  have hsubdim : s - k ≤ n - k := Nat.sub_le_sub_right hsn k
  rw [codeContainmentProbability, card_containingCodes P y hy hks,
    card_code_eq_gaussian_norm P hsubdim,
    card_code_eq_gaussian_norm P hsn]
  let q : ℝ := idealNorm P
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num)
    (two_le_idealNorm_real P)
  have hcorrpos : 0 < gaussianCorrection q n s :=
    (show 0 < (2 : ℝ)⁻¹ ^ s by positivity).trans_le
      (gaussianCorrection_lower_bound q (two_le_idealNorm_real P) hsn)
  have hspace : (n - k) - (s - k) = n - s := by omega
  have hexp : s * (n - s) =
      (s - k) * (n - s) + k * (n - s) := by
    calc
      s * (n - s) = ((s - k) + k) * (n - s) := by
        rw [Nat.sub_add_cancel hks]
      _ = (s - k) * (n - s) + k * (n - s) := by ring
  change
    q ^ ((s - k) * ((n - k) - (s - k))) *
          gaussianCorrection q (n - k) (s - k) /
        (q ^ (s * (n - s)) * gaussianCorrection q n s) =
      (q ^ (k * (n - s)))⁻¹ * codeContainmentCorrection P n s k
  rw [hspace, hexp, pow_add, codeContainmentCorrection]
  change
    q ^ ((s - k) * (n - s)) * gaussianCorrection q (n - k) (s - k) /
        (q ^ ((s - k) * (n - s)) * q ^ (k * (n - s)) *
          gaussianCorrection q n s) =
      (q ^ (k * (n - s)))⁻¹ *
        (gaussianCorrection q (n - k) (s - k) /
          gaussianCorrection q n s)
  field_simp [pow_ne_zero _ (ne_of_gt hqpos), ne_of_gt hcorrpos]

theorem codeContainmentError_bound (P : PrimeIdeal K)
    {n s k : ℕ} (_hks : k ≤ s) (hsn : s ≤ n) :
    |codeContainmentError P n s k| ≤
      ((((s - k : ℕ) : ℝ) * 2 ^ (s - k) + (s : ℝ) * 2 ^ s) * 2 ^ s) /
        (idealNorm P : ℝ) := by
  have hsubdim : s - k ≤ n - k := Nat.sub_le_sub_right hsn k
  exact gaussianCorrection_quotient_error_bound (idealNorm P : ℝ)
    (two_le_idealNorm_real P) hsubdim hsn

theorem codeContainmentProbability_asymptotic (P : PrimeIdeal K)
    {n s k : ℕ} (y : Fin k → (Fin n → residueField P))
    (hy : LinearIndependent (residueField P) y)
    (hks : k ≤ s) (hsn : s ≤ n) :
    codeContainmentProbability P n s k y =
        ((idealNorm P : ℝ) ^ (k * (n - s)))⁻¹ *
          (1 + codeContainmentError P n s k) ∧
      |codeContainmentError P n s k| ≤
        ((((s - k : ℕ) : ℝ) * 2 ^ (s - k) + (s : ℝ) * 2 ^ s) * 2 ^ s) /
          (idealNorm P : ℝ) := by
  constructor
  · rw [codeContainmentProbability_eq P y hy hks hsn]
    congr 1
    rw [codeContainmentError]
    ring
  · exact codeContainmentError_bound P hks hsn

theorem codeContainmentProbability_uniform
    {n s k : ℕ} (hks : k ≤ s) (hsn : s ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : PrimeIdeal K)
        (y : Fin k → (Fin n → residueField P)),
        LinearIndependent (residueField P) y →
        ∃ ε : ℝ,
          codeContainmentProbability P n s k y =
              ((idealNorm P : ℝ) ^ (k * (n - s)))⁻¹ * (1 + ε) ∧
            |ε| ≤ C / (idealNorm P : ℝ) := by
  let C₀ : ℝ :=
    (((s - k : ℕ) : ℝ) * 2 ^ (s - k) + (s : ℝ) * 2 ^ s) * 2 ^ s
  refine ⟨1 + C₀, by positivity, ?_⟩
  intro P y hy
  refine ⟨codeContainmentError P n s k,
    (codeContainmentProbability_asymptotic P y hy hks hsn).1, ?_⟩
  calc
    |codeContainmentError P n s k| ≤ C₀ / (idealNorm P : ℝ) := by
      exact codeContainmentError_bound P hks hsn
    _ ≤ (1 + C₀) / (idealNorm P : ℝ) := by
      apply div_le_div₀
      · positivity
      · linarith
      · exact lt_of_lt_of_le (by norm_num) (two_le_idealNorm_real P)
      · rfl

theorem containingCodes_eq_empty_of_lt (P : PrimeIdeal K) {n s k : ℕ}
    (y : Fin k → (Fin n → residueField P))
    (hy : LinearIndependent (residueField P) y)
    (hsk : s < k) :
    containingCodes P (n := n) (s := s) (k := k) y =
      (∅ : Finset (Code P n s)) := by
  classical
  rw [containingCodes, Finset.filter_eq_empty_iff]
  intro S _ hS
  have hdim : Module.finrank (residueField P) (codeSpan P y) ≤
      Module.finrank (residueField P) S.1 :=
    Submodule.finrank_mono hS
  have hks : k ≤ s := by
    calc
      k = Module.finrank (residueField P) (codeSpan P y) := by
        change k = Module.finrank (residueField P)
          (Submodule.span (residueField P) (Set.range y))
        simpa using (finrank_span_eq_card hy).symm
      _ ≤ Module.finrank (residueField P) S.1 := hdim
      _ = s := S.2
  exact (Nat.not_le_of_lt hsk) hks

theorem codeContainmentProbability_eq_zero_of_lt (P : PrimeIdeal K)
    {n s k : ℕ} (y : Fin k → (Fin n → residueField P))
    (hy : LinearIndependent (residueField P) y) (hsk : s < k) :
    codeContainmentProbability P n s k y = 0 := by
  rw [codeContainmentProbability,
    containingCodes_eq_empty_of_lt P (n := n) (s := s) (k := k) y hy hsk]
  simp

end
end Katznelson
