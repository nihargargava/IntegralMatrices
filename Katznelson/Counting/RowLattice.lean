import Katznelson.Counting.RowSpaces
import Mathlib.Algebra.Module.ZLattice.Covolume
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

open MeasureTheory Set
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

/- The paper's `H(D) = H(Λ_D)`. -/
noncomputable def rowSpaceHeight {m k : ℕ}
    (V : Grassmannian K m k) : ℝ :=
  ZLattice.covolume (rowZLattice V)
    (μHE[Module.finrank ℝ (rowRealSpan V)])

theorem rowSpaceHeight_pos {m k : ℕ} (V : Grassmannian K m k) :
    0 < rowSpaceHeight V := by
  exact ZLattice.covolume_pos (rowZLattice V)
    (μHE[Module.finrank ℝ (rowRealSpan V)])

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

end

end Katznelson
