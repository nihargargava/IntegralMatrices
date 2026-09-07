import Katznelson.Counting.Support
import Mathlib.RingTheory.Localization.Integer

/-!
# Rational row spaces

This is the subspace-indexed form of Proposition `pr:trijection` and Lemma
`le:new_bijection` in the paper.  A reduced echelon matrix is the canonical
coordinate representative of the corresponding point of the Grassmannian;
for proofs it is cleaner to index directly by that rational row space.
-/

namespace Katznelson

open Set
open scoped Classical NumberField nonZeroDivisors

section

variable {K : Type*} [Field K] [NumberField K]

/- The paper's `Gr(k,K^m)`. -/
abbrev Grassmannian (K : Type*) [Field K] (m k : ℕ) :=
  {V : Submodule K (Fin m → K) // Module.finrank K V = k}

/- The `K`-row space of an integral matrix. -/
noncomputable def matrixRowSpace {n m : ℕ} (A : IntegralMatrix K n m) :
    Submodule K (Fin m → K) :=
  Submodule.span K (Set.range (algebraicMatrix A).row)

theorem finrank_matrixRowSpace {n m : ℕ} (A : IntegralMatrix K n m) :
    Module.finrank K (matrixRowSpace A) = integralMatrixRank A := by
  rw [matrixRowSpace, integralMatrixRank, matrixRank,
    ← Matrix.rank_eq_finrank_span_row]

theorem algebraicMatrix_eq_zero_of_integralMatrixRank_eq_zero
    {n m : ℕ} (A : IntegralMatrix K n m)
    (hA : integralMatrixRank A = 0) :
    algebraicMatrix A = 0 := by
  have hspan :
      Submodule.span K (Set.range (algebraicMatrix A).row) = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    rw [← Matrix.rank_eq_finrank_span_row]
    exact hA
  ext i j
  have hi : (algebraicMatrix A).row i ∈
      Submodule.span K (Set.range (algebraicMatrix A).row) :=
    Submodule.subset_span (Set.mem_range_self i)
  rw [hspan] at hi
  simpa using congrFun (show (algebraicMatrix A).row i = 0 from hi) j

theorem integralMatrix_eq_zero_of_integralMatrixRank_eq_zero
    {n m : ℕ} (A : IntegralMatrix K n m)
    (hA : integralMatrixRank A = 0) :
    A = 0 := by
  have hAlg := algebraicMatrix_eq_zero_of_integralMatrixRank_eq_zero A hA
  ext i j
  simpa [algebraicMatrix] using
    congrArg (fun B : M n m K => B i j) hAlg

/- The point of `Gr(k,K^m)` attached to a rank-`k` matrix. -/
noncomputable def rowSpaceOfRank {n m k : ℕ}
    (A : {A : IntegralMatrix K n m // integralMatrixRank A = k}) :
    Grassmannian K m k :=
  ⟨matrixRowSpace A.1, by rw [finrank_matrixRowSpace, A.2]⟩

/- The primitive integral row module `Λ_D = V ∩ 𝓞_K^m`. -/
def integralRowModule {m k : ℕ} (V : Grassmannian K m k) :
    Submodule (𝓞 K) (Fin m → 𝓞 K) where
  carrier := {v | (fun j => (v j : K)) ∈ V.1}
  zero_mem' := by
    change (0 : Fin m → K) ∈ V.1
    exact V.1.zero_mem
  add_mem' := by
    intro x y hx hy
    change (fun j => ((x + y) j : K)) ∈ V.1
    convert V.1.add_mem hx hy using 1
    ext j
    simp
  smul_mem' := by
    intro a x hx
    change (fun j => ((a • x) j : K)) ∈ V.1
    convert V.1.smul_mem (a : K) hx using 1
    ext j
    simp [Pi.smul_apply]

omit [NumberField K] in
@[simp]
theorem mem_integralRowModule_iff {m k : ℕ}
    (V : Grassmannian K m k) (v : Fin m → 𝓞 K) :
    v ∈ integralRowModule V ↔ (fun j => (v j : K)) ∈ V.1 := Iff.rfl

/- The natural inclusion of the primitive integral row module into its
   rational row space. -/
def integralRowToRowSpace {m k : ℕ} (V : Grassmannian K m k) :
    integralRowModule V →ₗ[𝓞 K] V.1 where
  toFun v := ⟨fun j => (v.1 j : K), v.2⟩
  map_add' x y := by
    ext j
    simp
  map_smul' a x := by
    ext j
    change (a : K) * (x.1 j : K) = (a : K) * (x.1 j : K)
    rfl

omit [NumberField K] in
@[simp]
theorem integralRowToRowSpace_apply {m k : ℕ}
    (V : Grassmannian K m k) (v : integralRowModule V) (j : Fin m) :
    (integralRowToRowSpace V v : V.1).1 j = (v.1 j : K) := rfl

/- Clearing one common denominator in the finitely many coordinates shows
   that `V ∩ 𝓞_K^m` has full `K`-span in `V`.  This is the algebraic input
   behind the paper's assertion that `Λ_D` is a full lattice. -/
theorem span_range_integralRowToRowSpace {m k : ℕ}
    (V : Grassmannian K m k) :
    Submodule.span K
      (Set.range (fun v : integralRowModule V =>
        (integralRowToRowSpace V v : V.1))) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      (R := 𝓞 K) (S := K) (nonZeroDivisors (𝓞 K))
      (fun j : Fin m => x.1 j)
  let a : Fin m → 𝓞 K := fun j => (hb j).choose
  have ha (j : Fin m) : (a j : K) = (b.1 : K) * x.1 j := by
    simpa [a, IsLocalization.IsInteger, Algebra.smul_def] using
      (hb j).choose_spec
  let v : integralRowModule V := ⟨a, by
    change (fun j => (a j : K)) ∈ V.1
    have hx := V.1.smul_mem (b.1 : K) x.2
    convert hx using 1
    funext j
    exact ha j⟩
  have hv : (integralRowToRowSpace V v : V.1) ∈
      Submodule.span K
        (Set.range (fun w : integralRowModule V =>
          (integralRowToRowSpace V w : V.1))) :=
    Submodule.subset_span (Set.mem_range_self v)
  have hb0 : (b.1 : K) ≠ 0 := by
    exact NumberField.RingOfIntegers.coe_ne_zero_iff.mpr
      (nonZeroDivisors.coe_ne_zero b)
  have hxv : x = (b.1 : K)⁻¹ • (integralRowToRowSpace V v : V.1) := by
    apply Subtype.ext
    funext j
    change x.1 j = (b.1 : K)⁻¹ * (a j : K)
    rw [ha]
    simp [hb0]
  rw [hxv]
  exact Submodule.smul_mem _ _ hv

/- The `ℚ`-span of the primitive module is stable under multiplication by
   `K`: expand the multiplier in the integral basis of `K/ℚ` and absorb
   each integral basis vector into the `𝓞_K`-module. -/
theorem k_smul_mem_span_integralRows {m k : ℕ}
    (V : Grassmannian K m k) (c : K) (x : V.1)
    (hx : x ∈ Submodule.span ℚ
      (Set.range (fun v : integralRowModule V =>
        (integralRowToRowSpace V v : V.1)))) :
    c • x ∈ Submodule.span ℚ
      (Set.range (fun v : integralRowModule V =>
        (integralRowToRowSpace V v : V.1))) := by
  let W : Submodule ℚ V.1 := Submodule.span ℚ
    (Set.range (fun v : integralRowModule V =>
      (integralRowToRowSpace V v : V.1)))
  change c • x ∈ W
  change x ∈ W at hx
  refine Submodule.span_induction
    (p := fun y : V.1 => fun _ => c • y ∈ W) ?_ ?_ ?_ ?_ hx
  · intro _ hy
    obtain ⟨v, rfl⟩ := hy
    rw [← (NumberField.integralBasis K).sum_repr c, Finset.sum_smul]
    apply W.sum_mem
    intro i _
    have hgen : (integralRowToRowSpace V
        ((NumberField.RingOfIntegers.basis K i) • v) : V.1) ∈ W :=
      Submodule.subset_span (Set.mem_range_self _)
    have hterm := W.smul_mem ((NumberField.integralBasis K).repr c i) hgen
    simpa [NumberField.integralBasis_apply, smul_smul] using hterm
  · simp [W]
  · intro y z _ _ hy hz
    simpa [smul_add] using W.add_mem hy hz
  · intro q y _ hy
    rw [smul_comm c q y]
    exact W.smul_mem q hy

/- Since `𝓞_K` spans `K` over `ℚ`, full `K`-span also implies full
   rational span. -/
theorem span_range_integralRowToRowSpace_rat {m k : ℕ}
    (V : Grassmannian K m k) :
    Submodule.span ℚ
      (Set.range (fun v : integralRowModule V =>
        (integralRowToRowSpace V v : V.1))) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hxK : x ∈ Submodule.span K
      (Set.range (fun v : integralRowModule V =>
        (integralRowToRowSpace V v : V.1))) := by
    rw [span_range_integralRowToRowSpace V]
    trivial
  refine Submodule.span_induction (p := fun y : V.1 => fun _ =>
    y ∈ Submodule.span ℚ
      (Set.range (fun v : integralRowModule V =>
        (integralRowToRowSpace V v : V.1)))) ?_ ?_ ?_ ?_ hxK
  · exact fun _ hy => Submodule.subset_span hy
  · exact Submodule.zero_mem _
  · exact fun _ _ _ _ => Submodule.add_mem _
  · intro c y _ hy
    exact k_smul_mem_span_integralRows V c y hy

def rowsInIntegralRowModule {n m k : ℕ}
    (V : Grassmannian K m k) (A : IntegralMatrix K n m) : Prop :=
  ∀ i, A.row i ∈ integralRowModule V

theorem rowsInIntegralRowModule_iff_rowSpace_le {n m k : ℕ}
    (V : Grassmannian K m k) (A : IntegralMatrix K n m) :
    rowsInIntegralRowModule V A ↔ matrixRowSpace A ≤ V.1 := by
  rw [matrixRowSpace, Submodule.span_le]
  constructor
  · intro h _
    rintro ⟨i, rfl⟩
    exact h i
  · intro h i
    exact h (Set.mem_range_self i)

theorem integralMatrixRank_le_of_rowsInIntegralRowModule
    {n m k : ℕ} (V : Grassmannian K m k) (A : IntegralMatrix K n m)
    (hrows : rowsInIntegralRowModule V A) :
    integralMatrixRank A ≤ k := by
  have hle := Submodule.finrank_mono
    ((rowsInIntegralRowModule_iff_rowSpace_le V A).1 hrows)
  simpa [finrank_matrixRowSpace, V.2] using hle

theorem rowSpace_eq_of_rowsIn_of_rank {n m k : ℕ}
    (V : Grassmannian K m k) (A : IntegralMatrix K n m)
    (hrows : rowsInIntegralRowModule V A)
    (hrank : integralMatrixRank A = k) :
    matrixRowSpace A = V.1 := by
  apply Submodule.eq_of_le_of_finrank_le
  · exact (rowsInIntegralRowModule_iff_rowSpace_le V A).1 hrows
  · rw [V.2, finrank_matrixRowSpace, hrank]

theorem rowSpace_eq_iff_rank_eq_of_rowsIn {n m k : ℕ}
    (V : Grassmannian K m k) (A : IntegralMatrix K n m)
    (hrows : rowsInIntegralRowModule V A) :
    matrixRowSpace A = V.1 ↔ integralMatrixRank A = k := by
  constructor
  · intro hspace
    have hfin := congrArg
      (fun W : Submodule K (Fin m → K) => Module.finrank K W) hspace
    simpa [finrank_matrixRowSpace, V.2] using hfin
  · intro hrank
    exact rowSpace_eq_of_rowsIn_of_rank V A hrows hrank

theorem rowsInIntegralRowModule_of_rowSpace_eq {n m k : ℕ}
    (V : Grassmannian K m k) (A : IntegralMatrix K n m)
    (hspace : matrixRowSpace A = V.1) :
    rowsInIntegralRowModule V A := by
  rw [rowsInIntegralRowModule_iff_rowSpace_le, hspace]

/- Equation `eq:bijection`, with the echelon representative replaced by its
   equivalent Grassmannian point. -/
noncomputable def rankMatrixEquivRowSpaces {n m k : ℕ} :
    {A : IntegralMatrix K n m // integralMatrixRank A = k} ≃
      Σ V : Grassmannian K m k,
        {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A = k} where
  toFun A :=
    ⟨rowSpaceOfRank A,
      ⟨A.1, rowsInIntegralRowModule_of_rowSpace_eq _ _ rfl, A.2⟩⟩
  invFun VA := ⟨VA.2.1, VA.2.2.2⟩
  left_inv A := by
    rfl
  right_inv VA := by
    rcases VA with ⟨V, A, hrows, hrank⟩
    have hV : rowSpaceOfRank (⟨A, hrank⟩ :
        {A : IntegralMatrix K n m // integralMatrixRank A = k}) = V := by
      apply Subtype.ext
      exact rowSpace_eq_of_rowsIn_of_rank V A hrows hrank
    cases hV
    rfl

end

end Katznelson
