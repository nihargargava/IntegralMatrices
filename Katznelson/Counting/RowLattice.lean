import Katznelson.Counting.RowSpaces
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# The lattice attached to a rational row space

For `V ∈ Gr(k,K^m)`, this constructs the paper's primitive lattice
`Λ_D = V ∩ 𝓞_K^m`, embeds it in its real span, and defines its height as its
covolume.  The construction does not choose an echelon representative.
-/

namespace Katznelson

open MeasureTheory Set Module
open scoped Classical MeasureTheory NumberField

section

variable {K : Type*} [Field K] [NumberField K]

noncomputable def integralVectorEmbedding (m : ℕ) :
    (Fin m → 𝓞 K) →ₗ[ℤ] (Fin m → K_ℝ[K]) where
  toFun x j := numberEmbedding K (x j : K)
  map_add' x y := by
    funext j
    simpa only [Pi.add_apply, map_add] using
      numberEmbedding_add K (x j : K) (y j : K)
  map_smul' a x := by
    funext j
    change numberEmbedding K
        ((algebraMap (𝓞 K) K) (a • x j)) =
      a • numberEmbedding K (x j : K)
    rw [map_zsmul, numberEmbedding_zsmul]

@[simp]
theorem integralVectorEmbedding_apply (m : ℕ) (x : Fin m → 𝓞 K)
    (j : Fin m) :
    integralVectorEmbedding (K := K) m x j =
      numberEmbedding K (x j : K) := rfl

theorem integralVectorEmbedding_injective (m : ℕ) :
    Function.Injective (integralVectorEmbedding (K := K) m) := by
  intro x y hxy
  ext j
  apply numberEmbedding_injective K
  exact congrFun hxy j

/-! ## Rational-to-real dimension under the Minkowski embedding -/

abbrev IntegralBasisIndex (K : Type*) [Field K] [NumberField K] :=
  Module.Free.ChooseBasisIndex ℤ (𝓞 K)

/- Coordinates in the integral basis of `K/ℚ`, applied componentwise. -/
noncomputable def rationalVectorCoordinates (m : ℕ) :
    (Fin m → K) →ₗ[ℚ] (Fin m × IntegralBasisIndex K → ℚ) where
  toFun x p := (NumberField.integralBasis K).repr (x p.1) p.2
  map_add' x y := by
    funext p
    simp
  map_smul' q x := by
    funext p
    simp

theorem rationalVectorCoordinates_injective (m : ℕ) :
    Function.Injective (rationalVectorCoordinates (K := K) m) := by
  intro x y hxy
  funext j
  apply (NumberField.integralBasis K).repr.injective
  ext i
  exact congrFun hxy (j, i)

/- Real coordinates after transporting the Euclidean mixed space to
   Mathlib's ordinary mixed space. -/
noncomputable def realVectorCoordinates (m : ℕ) :
    (Fin m → K_ℝ[K]) →ₗ[ℝ]
      (Fin m × IntegralBasisIndex K → ℝ) where
  toFun x p := (NumberField.mixedEmbedding.latticeBasis K).repr
    (NumberField.mixedEmbedding.euclidean.toMixed K (x p.1)) p.2
  map_add' x y := by
    funext p
    simp
  map_smul' q x := by
    funext p
    simp

theorem realVectorCoordinates_injective (m : ℕ) :
    Function.Injective (realVectorCoordinates (K := K) m) := by
  intro x y hxy
  funext j
  apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
  apply (NumberField.mixedEmbedding.latticeBasis K).repr.injective
  ext i
  exact congrFun hxy (j, i)

theorem realVectorCoordinates_numberEmbedding (m : ℕ)
    (x : Fin m → K) (p : Fin m × IntegralBasisIndex K) :
    realVectorCoordinates (K := K) m
        (fun j => numberEmbedding K (x j)) p =
      algebraMap ℚ ℝ (rationalVectorCoordinates (K := K) m x p) := by
  exact NumberField.mixedEmbedding.latticeBasis_repr_apply K (x p.1) p.2

/- Extending rational coefficients to real coefficients introduces no new
   linear relations among Minkowski-embedded vectors. -/
theorem linearIndependent_numberEmbedding
    {ι : Type*} {m : ℕ} {u : ι → (Fin m → K)}
    (hu : LinearIndependent ℚ u) :
    LinearIndependent ℝ (fun i j => numberEmbedding K (u i j)) := by
  let qcoord := rationalVectorCoordinates (K := K) m
  let rcoord := realVectorCoordinates (K := K) m
  have hq : LinearIndependent ℚ (fun i => qcoord (u i)) :=
    hu.map' qcoord (LinearMap.ker_eq_bot.mpr
      (rationalVectorCoordinates_injective (K := K) m))
  have hr : LinearIndependent ℝ
      (fun i => algebraMap ℚ ℝ ∘ qcoord (u i)) :=
    linearIndependent_algebraMap_comp_iff.mpr hq
  have hr' : LinearIndependent ℝ
      (fun i => rcoord (fun j => numberEmbedding K (u i j))) := by
    convert hr using 1
    funext i p
    exact realVectorCoordinates_numberEmbedding (K := K) m (u i) p
  exact hr'.of_comp

/- The rational row space embedded coordinatewise in Minkowski space. -/
noncomputable def rowSpaceVectorEmbeddingQ {m k : ℕ}
    (V : Grassmannian K m k) :
    V.1 →ₗ[ℚ] (Fin m → K_ℝ[K]) where
  toFun x j := numberEmbedding K (x.1 j)
  map_add' x y := by
    funext j
    exact numberEmbedding_add K _ _
  map_smul' q x := by
    funext j
    exact numberEmbedding_rat_smul K q (x.1 j)

@[simp]
theorem rowSpaceVectorEmbeddingQ_apply {m k : ℕ}
    (V : Grassmannian K m k) (x : V.1) (j : Fin m) :
    rowSpaceVectorEmbeddingQ V x j = numberEmbedding K (x.1 j) := rfl

noncomputable def embeddedIntegralRowModule {m k : ℕ}
    (V : Grassmannian K m k) : Submodule ℤ (Fin m → K_ℝ[K]) :=
  (integralRowModule V).restrictScalars ℤ |>.map
    (integralVectorEmbedding (K := K) m)

theorem mem_embeddedIntegralRowModule_iff {m k : ℕ}
    (V : Grassmannian K m k) (x : Fin m → K_ℝ[K]) :
    x ∈ embeddedIntegralRowModule V ↔
      ∃ v ∈ integralRowModule V,
        integralVectorEmbedding (K := K) m v = x := by
  rfl

noncomputable instance embeddedIntegralRowModule.discreteTopology
    {m k : ℕ} (V : Grassmannian K m k) :
    DiscreteTopology (embeddedIntegralRowModule V) := by
  let L := NumberField.mixedEmbedding.euclidean.integerLattice K
  let _ : DiscreteTopology L := by
    dsimp [L]
    infer_instance
  let toProduct : embeddedIntegralRowModule V → (Fin m → L) := fun x j =>
    ⟨x.1 j, by
      obtain ⟨v, _, hv⟩ :=
        (mem_embeddedIntegralRowModule_iff V x.1).1 x.2
      rw [← hv]
      change numberEmbedding K (v j : K) ∈
        NumberField.mixedEmbedding.euclidean.integerLattice K
      change (NumberField.mixedEmbedding.euclidean.toMixed K)
          (numberEmbedding K (v j : K)) ∈
        NumberField.mixedEmbedding.integerLattice K
      exact ⟨v j, by simp [numberEmbedding]⟩⟩
  apply DiscreteTopology.of_continuous_injective
      (f := toProduct)
  · apply continuous_pi
    intro j
    apply Continuous.subtype_mk
    exact continuous_apply j |>.comp continuous_subtype_val
  · intro x y hxy
    apply Subtype.ext
    funext j
    exact congrArg Subtype.val (congrFun hxy j)

/- The real subspace `Λ_D ⊗_ℤ ℝ`. -/
noncomputable def rowRealSpan {m k : ℕ} (V : Grassmannian K m k) :
    Submodule ℝ (Fin m → K_ℝ[K]) :=
  Submodule.span ℝ (embeddedIntegralRowModule V : Set (Fin m → K_ℝ[K]))

/- Use the canonical Borel structure of the induced norm topology. -/
noncomputable local instance rowRealSpanMeasurableSpace {m k : ℕ}
    (V : Grassmannian K m k) : MeasurableSpace (rowRealSpan V) :=
  borel (rowRealSpan V)

local instance rowRealSpanBorelSpace {m k : ℕ}
    (V : Grassmannian K m k) : BorelSpace (rowRealSpan V) := ⟨rfl⟩

/- A rational basis of the row space gives a convenient basis for the real
   span after the Minkowski embedding. -/
abbrev RowSpaceBasisIndex {m k : ℕ} (V : Grassmannian K m k) :=
  Module.Free.ChooseBasisIndex ℚ V.1

noncomputable def rowSpaceBasisQ {m k : ℕ} (V : Grassmannian K m k) :
    Basis (RowSpaceBasisIndex V) ℚ V.1 :=
  Module.Free.chooseBasis ℚ V.1

noncomputable def embeddedRowBasisQ {m k : ℕ}
    (V : Grassmannian K m k) (i : RowSpaceBasisIndex V) :
    Fin m → K_ℝ[K] :=
  rowSpaceVectorEmbeddingQ V (rowSpaceBasisQ V i)

theorem embeddedRowBasisQ_linearIndependent {m k : ℕ}
    (V : Grassmannian K m k) :
    LinearIndependent ℝ (embeddedRowBasisQ V) := by
  letI : Module.Finite ℚ V.1 := FiniteDimensional.trans ℚ K V.1
  letI : Fintype (RowSpaceBasisIndex V) := Fintype.ofFinite _
  have hsub : LinearIndependent ℚ
      (fun i : RowSpaceBasisIndex V => (rowSpaceBasisQ V i : V.1).1) := by
    exact (rowSpaceBasisQ V).linearIndependent.map'
      (V.1.subtype.restrictScalars ℚ)
      (LinearMap.ker_eq_bot.mpr V.1.subtype_injective)
  exact linearIndependent_numberEmbedding hsub

theorem rowSpaceVectorEmbeddingQ_mem_rowRealSpan_of_mem_ratSpan
    {m k : ℕ} (V : Grassmannian K m k) (x : V.1)
    (hx : x ∈ Submodule.span ℚ
      (Set.range (fun v : integralRowModule V =>
        (integralRowToRowSpace V v : V.1)))) :
    rowSpaceVectorEmbeddingQ V x ∈ rowRealSpan V := by
  let W : Submodule ℚ (Fin m → K_ℝ[K]) :=
    (rowRealSpan V).restrictScalars ℚ
  change rowSpaceVectorEmbeddingQ V x ∈ W
  refine Submodule.span_induction (p := fun y : V.1 => fun _ =>
    rowSpaceVectorEmbeddingQ V y ∈ W) ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨v, rfl⟩ := hy
    apply Submodule.subset_span
    exact (mem_embeddedIntegralRowModule_iff V _).2
      ⟨v.1, v.2, rfl⟩
  · simpa using W.zero_mem
  · intro y z _ _ hy hz
    simpa using W.add_mem hy hz
  · intro q y _ hy
    simpa using W.smul_mem q hy

theorem rowSpaceVectorEmbeddingQ_mem_span_embeddedRowBasisQ
    {m k : ℕ} (V : Grassmannian K m k) (x : V.1) :
    rowSpaceVectorEmbeddingQ V x ∈
      Submodule.span ℝ (Set.range (embeddedRowBasisQ V)) := by
  letI : Module.Finite ℚ V.1 := FiniteDimensional.trans ℚ K V.1
  letI : Fintype (RowSpaceBasisIndex V) := Fintype.ofFinite _
  let b := rowSpaceBasisQ V
  let W := Submodule.span ℝ (Set.range (embeddedRowBasisQ V))
  rw [← b.sum_repr x]
  change rowSpaceVectorEmbeddingQ V
      (∑ i, (b.repr x) i • b i) ∈ W
  rw [map_sum]
  apply W.sum_mem
  intro i hi
  rw [map_smul]
  exact W.smul_mem ((b.repr x) i)
    (Submodule.subset_span (Set.mem_range_self i))

theorem rowRealSpan_eq_span_embeddedRowBasisQ {m k : ℕ}
    (V : Grassmannian K m k) :
    rowRealSpan V =
      Submodule.span ℝ (Set.range (embeddedRowBasisQ V)) := by
  apply le_antisymm
  · rw [rowRealSpan, Submodule.span_le]
    intro y hy
    obtain ⟨v, hv, rfl⟩ :=
      (mem_embeddedIntegralRowModule_iff V y).1 hy
    let x : V.1 := integralRowToRowSpace V ⟨v, hv⟩
    exact rowSpaceVectorEmbeddingQ_mem_span_embeddedRowBasisQ V x
  · rw [Submodule.span_le]
    intro y hy
    obtain ⟨i, rfl⟩ := hy
    apply rowSpaceVectorEmbeddingQ_mem_rowRealSpan_of_mem_ratSpan V
    rw [span_range_integralRowToRowSpace_rat V]
    trivial

theorem rowRealSpan_finrank {m k : ℕ} (V : Grassmannian K m k) :
    Module.finrank ℝ (rowRealSpan V) = k * degree K := by
  letI : Module.Finite ℚ V.1 := FiniteDimensional.trans ℚ K V.1
  letI : Fintype (RowSpaceBasisIndex V) := Fintype.ofFinite _
  rw [rowRealSpan_eq_span_embeddedRowBasisQ V,
    finrank_span_eq_card (embeddedRowBasisQ_linearIndependent V),
    ← Module.finrank_eq_card_chooseBasisIndex ℚ V.1,
    ← Module.finrank_mul_finrank ℚ K V.1, V.2]
  simp [degree, Nat.mul_comm]

/- The same lattice, now regarded as a full lattice in its real span. -/
noncomputable def rowZLattice {m k : ℕ} (V : Grassmannian K m k) :
    Submodule ℤ (rowRealSpan V) :=
  Submodule.comap ((rowRealSpan V).subtype.restrictScalars ℤ)
    (embeddedIntegralRowModule V)

noncomputable instance rowZLattice.discreteTopology {m k : ℕ}
    (V : Grassmannian K m k) : DiscreteTopology (rowZLattice V) := by
  let toAmbient : rowZLattice V → embeddedIntegralRowModule V :=
    fun x => ⟨x.1.1, x.2⟩
  apply DiscreteTopology.of_continuous_injective (f := toAmbient)
  · apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : embeddedIntegralRowModule V => z.1) hxy

noncomputable instance rowZLattice.isZLattice {m k : ℕ}
    (V : Grassmannian K m k) : IsZLattice ℝ (rowZLattice V) := by
  constructor
  change Submodule.span ℝ
      (Subtype.val ⁻¹' (embeddedIntegralRowModule V : Set (Fin m → K_ℝ[K]))) = ⊤
  exact eq_top_iff.mpr Submodule.span_span_coe_preimage.symm.le

/- The paper's `H(D) = H(Λ_D)`.  This is the covolume height used in the
   checked-in manuscript (Definition `de:height_definition`, lines 412--420)
   and is the lattice realization of Schmidt's subspace height.  Schmidt's
   1967 paper supplies the original height-counting argument; Thunder's 1992
   paper supplies a sharper asymptotic for the same height-counting problem. -/
noncomputable def rowSpaceHeight {m k : ℕ}
    (V : Grassmannian K m k) : ℝ :=
  ZLattice.covolume (rowZLattice V)
    (μHE[Module.finrank ℝ (rowRealSpan V)])

theorem rowSpaceHeight_pos {m k : ℕ} (V : Grassmannian K m k) :
    0 < rowSpaceHeight V := by
  exact ZLattice.covolume_pos (rowZLattice V)
    (μHE[Module.finrank ℝ (rowRealSpan V)])

/- The one-row lattice has the expected integral rank.  This is the
   dimension input for the lattice p-series estimates used in the paper's
   successive-minima and low-rank summations. -/
theorem rowZLattice_finrank {m k : ℕ} (V : Grassmannian K m k) :
    Module.finrank ℤ (rowZLattice V) = k * degree K := by
  rw [ZLattice.rank (K := ℝ) (rowZLattice V), rowRealSpan_finrank V]

/- A genuine lattice-series consequence of the preceding rank computation.
   The strict inequality records the noncritical range; when `(n-k)d = 1`
   the corresponding series is harmonic, which is precisely where the paper
   retains a logarithm. -/
theorem summable_rowZLattice_norm_inv_pow
    {m k n : ℕ} (V : Grassmannian K m k)
    (hgap : k * degree K < n * degree K - 1) :
    Summable (fun v : rowZLattice V =>
      ‖(v : rowRealSpan V)‖⁻¹ ^ (n * degree K - 1)) := by
  apply ZLattice.summable_norm_pow_inv (rowZLattice V)
  simpa [rowZLattice_finrank V] using hgap

theorem summable_rowZLattice_norm_inv_pow_of_gap
    {m k n : ℕ} (V : Grassmannian K m k)
    (hgap : 1 < (n - k) * degree K) :
    Summable (fun v : rowZLattice V =>
      ‖(v : rowRealSpan V)‖⁻¹ ^ (n * degree K - 1)) := by
  have hkn : k ≤ n := by
    by_contra hkn
    have hnk : n ≤ k := Nat.le_of_not_ge hkn
    have hzero : n - k = 0 := Nat.sub_eq_zero_of_le hnk
    simp [hzero] at hgap
  rw [Nat.sub_mul] at hgap
  apply summable_rowZLattice_norm_inv_pow V
  omega

/-! ## Matrices whose rows lie in the primitive row module -/

noncomputable def integralMatrixEmbedding (n m : ℕ) :
    IntegralMatrix K n m →ₗ[ℤ] M n m (K_ℝ[K]) where
  toFun := embedMatrix
  map_add' A B := by
    apply Matrix.ext
    intro i j
    exact numberEmbedding_add K _ _
  map_smul' z A := by
    apply Matrix.ext
    intro i j
    change numberEmbedding K
        ((algebraMap (𝓞 K) K) (z • (A i j))) =
      z • numberEmbedding K (A i j : K)
    rw [map_zsmul, numberEmbedding_zsmul]

@[simp]
theorem integralMatrixEmbedding_apply {n m : ℕ}
    (A : IntegralMatrix K n m) (i : Fin n) (j : Fin m) :
    integralMatrixEmbedding (K := K) n m A i j =
      numberEmbedding K (A i j : K) := rfl

theorem integralMatrixEmbedding_injective (n m : ℕ) :
    Function.Injective (integralMatrixEmbedding (K := K) n m) := by
  intro A B hAB
  ext i j
  apply numberEmbedding_injective K
  exact congrArg (fun C : M n m (K_ℝ[K]) => C i j) hAB

/- The O_K-module M_n(Λ_D) from Definition de:defi_of_M_t. -/
def integralRowMatrixModule {m k : ℕ} (V : Grassmannian K m k) (n : ℕ) :
    Submodule (𝓞 K) (IntegralMatrix K n m) where
  carrier := {A | rowsInIntegralRowModule V A}
  zero_mem' := by
    intro i
    exact (integralRowModule V).zero_mem
  add_mem' := by
    intro A B hA hB i
    exact (integralRowModule V).add_mem (hA i) (hB i)
  smul_mem' := by
    intro a A hA i
    exact (integralRowModule V).smul_mem a (hA i)

@[simp]
theorem mem_integralRowMatrixModule_iff {m k n : ℕ}
    (V : Grassmannian K m k) (A : IntegralMatrix K n m) :
    A ∈ integralRowMatrixModule V n ↔ rowsInIntegralRowModule V A := Iff.rfl

noncomputable def embeddedRowMatrixModule {m k : ℕ}
    (V : Grassmannian K m k) (n : ℕ) :
    Submodule ℤ (M n m (K_ℝ[K])) :=
  (integralRowMatrixModule V n).restrictScalars ℤ |>.map
    (integralMatrixEmbedding (K := K) n m)

theorem mem_embeddedRowMatrixModule_iff {m k n : ℕ}
    (V : Grassmannian K m k) (A : M n m (K_ℝ[K])) :
    A ∈ embeddedRowMatrixModule V n ↔
      ∃ B : IntegralMatrix K n m, rowsInIntegralRowModule V B ∧
        embedMatrix B = A := by
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact ⟨B, hB, rfl⟩
  · rintro ⟨B, hB, rfl⟩
    exact ⟨B, hB, rfl⟩

theorem mem_embeddedRowMatrixModule_iff_rows {m k n : ℕ}
    (V : Grassmannian K m k) (A : M n m (K_ℝ[K])) :
    A ∈ embeddedRowMatrixModule V n ↔
      ∀ i, A i ∈ embeddedIntegralRowModule V := by
  constructor
  · rintro ⟨B, hB, rfl⟩ i
    exact (mem_embeddedIntegralRowModule_iff V (embedMatrix B i)).2
      ⟨B.row i, hB i, rfl⟩
  · intro hA
    choose v hv using fun i =>
      (mem_embeddedIntegralRowModule_iff V (A i)).1 (hA i)
    let B : IntegralMatrix K n m := fun i => v i
    have hB : rowsInIntegralRowModule V B := by
      intro i
      exact (hv i).1
    have hBA : embedMatrix B = A := by
      ext i j
      exact congrFun (hv i).2 j
    exact (mem_embeddedRowMatrixModule_iff V A).2 ⟨B, hB, hBA⟩

noncomputable instance embeddedRowMatrixModule.discreteTopology
    {m k : ℕ} (V : Grassmannian K m k) (n : ℕ) :
    DiscreteTopology (embeddedRowMatrixModule V n) := by
  let L := NumberField.mixedEmbedding.euclidean.integerLattice K
  let _ : DiscreteTopology L := by
    dsimp [L]
    infer_instance
  let toProduct : embeddedRowMatrixModule V n → (Fin n → Fin m → L) :=
    fun A i j => ⟨A.1 i j, by
      obtain ⟨B, -, hB⟩ :=
        (mem_embeddedRowMatrixModule_iff V A.1).1 A.2
      rw [← hB]
      change numberEmbedding K (B i j : K) ∈
        NumberField.mixedEmbedding.euclidean.integerLattice K
      change (NumberField.mixedEmbedding.euclidean.toMixed K)
          (numberEmbedding K (B i j : K)) ∈
        NumberField.mixedEmbedding.integerLattice K
      exact ⟨B i j, by simp [numberEmbedding]⟩⟩
  apply DiscreteTopology.of_continuous_injective (f := toProduct)
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    apply Continuous.subtype_mk
    exact (continuous_apply j).comp
      ((continuous_apply i).comp continuous_subtype_val)
  · intro A B hAB
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    exact congrArg Subtype.val (congrFun (congrFun hAB i) j)

/- The real span, realized inside the actual Frobenius-normed matrix space. -/
noncomputable def rowMatrixRealSpan {m k : ℕ}
    (V : Grassmannian K m k) (n : ℕ) :
    Submodule ℝ (M n m (K_ℝ[K])) :=
  Submodule.span ℝ
    (embeddedRowMatrixModule V n : Set (M n m (K_ℝ[K])))

noncomputable instance rowMatrixRealSpanMeasurableSpace {m k : ℕ}
    (V : Grassmannian K m k) (n : ℕ) :
    MeasurableSpace (rowMatrixRealSpan V n) := borel (rowMatrixRealSpan V n)

instance rowMatrixRealSpanBorelSpace {m k : ℕ}
    (V : Grassmannian K m k) (n : ℕ) :
    BorelSpace (rowMatrixRealSpan V n) := ⟨rfl⟩

/- The rowwise submodule of matrices whose rows lie in the real row span. -/
def rowMatrixRowwiseSubmodule {m k n : ℕ}
    (V : Grassmannian K m k) :
    Submodule ℝ (M n m (K_ℝ[K])) where
  carrier := {A | ∀ i, A i ∈ rowRealSpan V}
  zero_mem' := by
    intro i
    exact (rowRealSpan V).zero_mem
  add_mem' := by
    intro A B hA hB i
    exact (rowRealSpan V).add_mem (hA i) (hB i)
  smul_mem' := by
    intro c A hA i
    exact (rowRealSpan V).smul_mem c (hA i)

@[simp]
theorem mem_rowMatrixRowwiseSubmodule_iff {m k n : ℕ}
    (V : Grassmannian K m k) (A : M n m (K_ℝ[K])) :
    A ∈ rowMatrixRowwiseSubmodule V ↔ ∀ i, A i ∈ rowRealSpan V := Iff.rfl

/- The real span of the matrix module is the product of the row spans. -/
theorem rowMatrixRealSpan_eq_rowwise {m k n : ℕ}
    (V : Grassmannian K m k) :
    rowMatrixRealSpan V n = rowMatrixRowwiseSubmodule V := by
  classical
  apply le_antisymm
  · rw [rowMatrixRealSpan, Submodule.span_le]
    intro A hA i
    obtain ⟨B, hB, rfl⟩ :=
      (mem_embeddedRowMatrixModule_iff V A).1 hA
    apply Submodule.subset_span
    exact (mem_embeddedIntegralRowModule_iff V _).2
      ⟨B.row i, hB i, rfl⟩
  · intro A hA
    have hsingle (i : Fin n) {x : Fin m → K_ℝ[K]}
        (hx : x ∈ rowRealSpan V) :
        Pi.single i x ∈ rowMatrixRealSpan V n := by
      rw [rowRealSpan] at hx
      refine Submodule.span_induction (p := fun y _ =>
        Pi.single i y ∈ rowMatrixRealSpan V n) ?_ ?_ ?_ ?_ hx
      · intro y hy
        obtain ⟨v, hv, rfl⟩ :=
          (mem_embeddedIntegralRowModule_iff V _).1 hy
        have hB : rowsInIntegralRowModule V
            (Pi.single i v : IntegralMatrix K n m) := by
          intro j
          change (Pi.single i v : IntegralMatrix K n m) j ∈
            integralRowModule V
          by_cases hji : j = i
          · subst j
            simpa using hv
          · simp [Pi.single_apply, hji]
        have hgen : embedMatrix (Pi.single i v : IntegralMatrix K n m) ∈
            embeddedRowMatrixModule V n :=
          (mem_embeddedRowMatrixModule_iff V _).2
            ⟨(Pi.single i v : IntegralMatrix K n m), hB, rfl⟩
        have hspan : embedMatrix (Pi.single i v : IntegralMatrix K n m) ∈
            rowMatrixRealSpan V n := Submodule.subset_span hgen
        have hmatrix :
            (Pi.single i (integralVectorEmbedding (K := K) m v) :
              M n m (K_ℝ[K])) =
              embedMatrix (Pi.single i v : IntegralMatrix K n m) := by
          ext j l
          by_cases hji : j = i
          · subst j
            simp [embedMatrix]
          · simp [embedMatrix, Pi.single_apply, hji]
        rw [hmatrix]
        exact hspan
      · have hzero : Pi.single i (0 : Fin m → K_ℝ[K]) =
            (0 : M n m (K_ℝ[K])) := by
          ext j l
          simp
        rw [hzero]
        exact (rowMatrixRealSpan V n).zero_mem
      · intro y z _ _ hy hz
        have hadd : (Pi.single i (y + z) : M n m (K_ℝ[K])) =
            (Pi.single i y : M n m (K_ℝ[K])) + Pi.single i z := by
          ext j l
          by_cases hji : j = i
          · subst j
            simp
          · simp [Pi.single_apply, hji]
        have h := (rowMatrixRealSpan V n).add_mem hy hz
        rw [hadd]
        exact h
      · intro c y _ hy
        have hsmul : (Pi.single i (c • y) : M n m (K_ℝ[K])) =
            c • (Pi.single i y : M n m (K_ℝ[K])) := by
          ext j l
          by_cases hji : j = i
          · subst j
            simp
          · simp [Pi.single_apply, hji]
        have h := (rowMatrixRealSpan V n).smul_mem c hy
        rw [hsmul]
        exact h
    change ∀ i, A i ∈ rowRealSpan V at hA
    rw [show A = ∑ i : Fin n, Pi.single i (A i) by
      exact (Finset.univ_sum_single A).symm]
    apply Submodule.sum_mem
    intro i hi
    exact hsingle i (hA i)

noncomputable def rowMatrixRealSpanEquiv {m k n : ℕ}
    (V : Grassmannian K m k) :
    rowMatrixRealSpan V n ≃ₗ[ℝ] (Fin n → rowRealSpan V) := by
  let e : rowMatrixRealSpan V n ≃ₗ[ℝ] (Fin n → rowRealSpan V) := {
    toFun := fun A i =>
      ⟨A.1 i, by
        have hA : (A : M n m (K_ℝ[K])) ∈
            rowMatrixRowwiseSubmodule V := by
          rw [← rowMatrixRealSpan_eq_rowwise V]
          exact A.2
        exact hA i⟩
    invFun := fun A =>
      ⟨fun i => (A i).1, by
        rw [rowMatrixRealSpan_eq_rowwise V]
        intro i
        exact (A i).2⟩
    map_add' := by
      intro A B
      ext i j
      rfl
    map_smul' := by
      intro c A
      ext i j
      rfl
    left_inv := by
      intro A
      apply Subtype.ext
      funext i
      rfl
    right_inv := by
      intro A
      ext i j
      rfl }
  exact e

theorem rowMatrixRealSpan_finrank {m k n : ℕ}
    (V : Grassmannian K m k) :
    Module.finrank ℝ (rowMatrixRealSpan V n) =
      n * (k * degree K) := by
  rw [(rowMatrixRealSpanEquiv V).finrank_eq,
    Module.finrank_pi_fintype ℝ]
  simp [rowRealSpan_finrank, Finset.sum_const, Fintype.card_fin,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem rowMatrixRealSpan_ne_bot_of_pos {m k n : ℕ}
    (V : Grassmannian K m k) (hk : 0 < k) (hn : 0 < n) :
    rowMatrixRealSpan V n ≠ ⊥ := by
  intro hbot
  have hfin : Module.finrank ℝ (rowMatrixRealSpan V n) = 0 := by
    rw [hbot]
    simp
  rw [rowMatrixRealSpan_finrank V] at hfin
  exact (Nat.ne_of_gt (Nat.mul_pos hn
    (Nat.mul_pos hk Module.finrank_pos))) hfin

noncomputable def rowMatrixZLattice {m k : ℕ}
    (V : Grassmannian K m k) (n : ℕ) :
    Submodule ℤ (rowMatrixRealSpan V n) :=
  Submodule.comap ((rowMatrixRealSpan V n).subtype.restrictScalars ℤ)
    (embeddedRowMatrixModule V n)

noncomputable instance rowMatrixZLattice.discreteTopology
    {m k : ℕ} (V : Grassmannian K m k) (n : ℕ) :
    DiscreteTopology (rowMatrixZLattice V n) := by
  let toAmbient : rowMatrixZLattice V n → embeddedRowMatrixModule V n :=
    fun A => ⟨A.1.1, A.2⟩
  apply DiscreteTopology.of_continuous_injective (f := toAmbient)
  · apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  · intro A B hAB
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun C : embeddedRowMatrixModule V n => C.1) hAB

theorem rowMatrixZLattice_span_top {m k : ℕ}
    (V : Grassmannian K m k) (n : ℕ) :
    Submodule.span ℝ
      (rowMatrixZLattice V n : Set (rowMatrixRealSpan V n)) = ⊤ := by
  change Submodule.span ℝ
      (Subtype.val ⁻¹'
        (embeddedRowMatrixModule V n : Set (M n m (K_ℝ[K])))) = ⊤
  exact eq_top_iff.mpr Submodule.span_span_coe_preimage.symm.le

/- The integral matrix lattice is the finite product of the corresponding
   one-row lattices.  This is the algebraic part of the product-covolume
   observation in Lemma `le:without_rank_cond`. -/
noncomputable def rowMatrixZLatticeEquiv {m k n : ℕ}
    (V : Grassmannian K m k) :
    rowMatrixZLattice V n ≃ₗ[ℤ] (Fin n → rowZLattice V) := by
  let e : rowMatrixZLattice V n ≃ₗ[ℤ] (Fin n → rowZLattice V) := {
    toFun := fun A i =>
      ⟨⟨A.1.1 i, by
          have hA : (A.1.1 : M n m (K_ℝ[K])) ∈ rowMatrixRealSpan V n := A.1.2
          have hEq := congrArg
            (fun W : Submodule ℝ (M n m (K_ℝ[K])) =>
              (A.1.1 : M n m (K_ℝ[K])) ∈ W)
            (rowMatrixRealSpan_eq_rowwise (n := n) V)
          have hA' : (A.1.1 : M n m (K_ℝ[K])) ∈
              rowMatrixRowwiseSubmodule V := hEq.mp hA
          exact (mem_rowMatrixRowwiseSubmodule_iff V _).mp hA' i⟩,
        by
          change (A.1.1 : M n m (K_ℝ[K])) i ∈
            embeddedIntegralRowModule V
          exact (mem_embeddedRowMatrixModule_iff_rows V
            (A.1.1 : M n m (K_ℝ[K]))).1 A.2 i⟩
    invFun := fun A =>
      let b : M n m (K_ℝ[K]) := fun i => (A i).1.1
      ⟨⟨b, by
          rw [rowMatrixRealSpan_eq_rowwise (n := n) V]
          intro i
          exact (A i).1.2⟩,
        by
          change b ∈ embeddedRowMatrixModule V n
          rw [mem_embeddedRowMatrixModule_iff_rows V b]
          intro i
          have hi : (A i).1 ∈ rowZLattice V := (A i).2
          change ((A i).1 : Fin m → K_ℝ[K]) ∈
            embeddedIntegralRowModule V at hi
          simpa [b] using hi⟩
    map_add' := by
      intro A B
      ext i j
      rfl
    map_smul' := by
      intro c A
      ext i j
      rfl
    left_inv := by
      intro A
      apply Subtype.ext
      apply Subtype.ext
      funext i
      rfl
    right_inv := by
      intro A
      ext i j
      rfl }
  exact e

/- The matrix lattice has one copy of the primitive row lattice for each of
   the `n` rows.  This is the dimension calculation used when applying the
   lattice p-series estimate to the unrestricted matrix sum. -/
theorem rowMatrixZLattice_finrank {m k n : ℕ}
    (V : Grassmannian K m k) :
    Module.finrank ℤ (rowMatrixZLattice V n) = n * (k * degree K) := by
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) :=
    rowMatrixZLattice.discreteTopology V n
  let hZ : @IsZLattice ℝ inferInstance (rowMatrixRealSpan V n)
      inferInstance inferInstance (rowMatrixZLattice V n) hdisc :=
    @IsZLattice.mk ℝ inferInstance (rowMatrixRealSpan V n)
      inferInstance inferInstance (rowMatrixZLattice V n) hdisc
      (by
        exact rowMatrixZLattice_span_top V n)
  have hrank : Module.finrank ℤ (rowMatrixZLattice V n) =
      Module.finrank ℝ (rowMatrixRealSpan V n) :=
    @ZLattice.rank ℝ inferInstance inferInstance inferInstance inferInstance
      inferInstance (rowMatrixRealSpan V n) inferInstance inferInstance
      inferInstance inferInstance (rowMatrixZLattice V n) hdisc hZ
  rw [hrank, rowMatrixRealSpan_finrank]

theorem summable_rowMatrixZLattice_norm_inv_pow
    {m k n p : ℕ} (V : Grassmannian K m k)
    (hgap : n * (k * degree K) < p) :
    Summable (fun A : rowMatrixZLattice V n =>
      ‖(A : rowMatrixRealSpan V n)‖⁻¹ ^ p) := by
  exact @ZLattice.summable_norm_pow_inv (rowMatrixRealSpan V n)
    inferInstance inferInstance inferInstance (rowMatrixZLattice V n)
    (rowMatrixZLattice.discreteTopology V n) p
    (by simpa [rowMatrixZLattice_finrank V] using hgap)

@[simp]
theorem rowMatrixZLatticeEquiv_coe {m k n : ℕ}
    (V : Grassmannian K m k) (A : rowMatrixZLattice V n) (i : Fin n) :
    ((rowMatrixZLatticeEquiv V A i : rowZLattice V) : Fin m → K_ℝ[K]) =
      ((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K])) i := by
  rfl

/- The inner summation set in Lemma `le:new_bijection` is exactly the
underlying set of the matrix row lattice. -/
noncomputable def integralRowMatricesEquivRowMatrixZLattice {m k : ℕ}
    (V : Grassmannian K m k) (n : ℕ) :
    {A : IntegralMatrix K n m // rowsInIntegralRowModule V A} ≃
      rowMatrixZLattice V n := by
  let e : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A} →
      rowMatrixZLattice V n := fun A =>
    ⟨⟨embedMatrix A.1, Submodule.subset_span ⟨A.1, A.2, rfl⟩⟩,
      ⟨A.1, A.2, rfl⟩⟩
  apply Equiv.ofBijective e
  constructor
  · intro A B hAB
    apply Subtype.ext
    apply integralMatrixEmbedding_injective (K := K) n m
    exact congrArg (fun C : rowMatrixZLattice V n =>
      ((C.1 : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))) hAB
  · intro A
    obtain ⟨B, hB, hBA⟩ :=
      (mem_embeddedRowMatrixModule_iff V A.1.1).1 A.2
    refine ⟨⟨B, hB⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hBA

@[simp]
theorem integralRowMatricesEquivRowMatrixZLattice_coe {m k : ℕ}
    (V : Grassmannian K m k) (n : ℕ)
    (A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A}) :
    (((integralRowMatricesEquivRowMatrixZLattice V n A :
      rowMatrixZLattice V n) : rowMatrixRealSpan V n) : M n m (K_ℝ[K])) =
        embedMatrix A.1 := by
  rfl

/- Transport the algebraic rank to the abstract lattice, so the rank
   restriction in the paper's `M_n(Λ_D)` can be stated on lattice points. -/
noncomputable def rowMatrixRank {m k n : ℕ}
    (V : Grassmannian K m k) (A : rowMatrixZLattice V n) : ℕ :=
  integralMatrixRank
    ((integralRowMatricesEquivRowMatrixZLattice V n).symm A).1

theorem rowMatrixRank_le {m k n : ℕ}
    (V : Grassmannian K m k) (A : rowMatrixZLattice V n) :
    rowMatrixRank V A ≤ k := by
  let B := (integralRowMatricesEquivRowMatrixZLattice V n).symm A
  simpa [rowMatrixRank, B] using
    integralMatrixRank_le_of_rowsInIntegralRowModule V B.1 B.2

theorem rowMatrixRank_eq_iff_rowSpace_eq {m k n : ℕ}
    (V : Grassmannian K m k) (A : rowMatrixZLattice V n) :
    rowMatrixRank V A = k ↔
      matrixRowSpace ((integralRowMatricesEquivRowMatrixZLattice V n).symm A).1 = V.1 := by
  let B := (integralRowMatricesEquivRowMatrixZLattice V n).symm A
  change integralMatrixRank B.1 = k ↔ matrixRowSpace B.1 = V.1
  exact (rowSpace_eq_iff_rank_eq_of_rowsIn V B.1 B.2).symm

noncomputable def rankIntegralRowMatricesEquivRowMatrixZLattice
    {m k n : ℕ} (V : Grassmannian K m k) :
    {A : IntegralMatrix K n m //
      rowsInIntegralRowModule V A ∧ integralMatrixRank A = k} ≃
      {A : rowMatrixZLattice V n // rowMatrixRank V A = k} := by
  let e := integralRowMatricesEquivRowMatrixZLattice V n
  let φ : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule V A ∧ integralMatrixRank A = k} →
      {A : rowMatrixZLattice V n // rowMatrixRank V A = k} := fun A =>
    ⟨e ⟨A.1, A.2.1⟩, by
      simpa [rowMatrixRank, e] using A.2.2⟩
  apply Equiv.ofBijective φ
  constructor
  · intro A B hAB
    apply Subtype.ext
    have hAB' := congrArg Subtype.val hAB
    change e ⟨A.1, A.2.1⟩ = e ⟨B.1, B.2.1⟩ at hAB'
    have hsrc :
        (⟨A.1, A.2.1⟩ :
          {A : IntegralMatrix K n m // rowsInIntegralRowModule V A}) =
        ⟨B.1, B.2.1⟩ := e.injective hAB'
    exact congrArg (fun X : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule V A} => X.1) hsrc
  · intro A
    let B := e.symm A.1
    have hB : integralMatrixRank B.1 = k := by
      simpa [B, rowMatrixRank, e] using A.2
    refine ⟨⟨B.1, ⟨B.2, hB⟩⟩, ?_⟩
    apply Subtype.ext
    change e ⟨B.1, B.2⟩ = A.1
    simpa [B] using e.apply_symm_apply A.1

@[simp]
theorem rankIntegralRowMatricesEquivRowMatrixZLattice_coe
    {m k n : ℕ} (V : Grassmannian K m k)
    (A : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule V A ∧ integralMatrixRank A = k}) :
    ((((rankIntegralRowMatricesEquivRowMatrixZLattice V A).1 :
      rowMatrixZLattice V n) : rowMatrixRealSpan V n) :
        M n m (K_ℝ[K])) = embedMatrix A.1 := by
  rfl

end

end Katznelson
