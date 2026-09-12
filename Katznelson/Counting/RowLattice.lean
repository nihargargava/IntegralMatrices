import Katznelson.Counting.RowSpaces
import Katznelson.Lattice
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.Order.PiLex

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

/- [Lean infrastructure] A row vector is a finite `l²` product.  The ordinary
   function type has Mathlib's supremum norm, so it cannot be used for the
   Euclidean geometry fixed in the paper (the norm is specified in the paper's
   equation (1)).  `PiLp 2` has the same underlying evaluations but the
   required Euclidean norm. -/
abbrev RowVector (K : Type*) [Field K] [NumberField K] (m : ℕ) :=
  PiLp 2 (fun _ : Fin m => K_ℝ[K])

noncomputable def rowVectorOfFun {m : ℕ} (x : Fin m → K_ℝ[K]) : RowVector K m :=
  WithLp.toLp 2 x

@[simp]
theorem rowVectorOfFun_apply {m : ℕ} (x : Fin m → K_ℝ[K]) (j : Fin m) :
    rowVectorOfFun x j = x j := rfl

@[simp]
theorem rowVectorOfFun_ofLp {m : ℕ} (x : RowVector K m) :
    rowVectorOfFun x.ofLp = x := by
  cases x
  rfl

/- [Lean infrastructure] The finite `l²` row representation has real
   dimension `m * degree K`.  This fixes the dimension normalization used by
   the paper's row-lattice estimates. -/
theorem rowVector_finrank {m : ℕ} :
    Module.finrank ℝ (RowVector K m) = m * degree K := by
  rw [(WithLp.linearEquiv 2 ℝ (Fin m → KReal K)).finrank_eq,
    Module.finrank_pi_fintype, NumberField.mixedEmbedding.euclidean.finrank]
  rw [Finset.sum_const]
  simp [degree]

/- [Lean infrastructure] The Euclidean norm of a row of a Frobenius matrix is
   bounded by the matrix norm.  This is the normalization-correct version of
   the elementary row estimate needed when `D ∈ 𝓕_k(T)` supplies a bounded
   matrix. -/
theorem norm_rowVectorOfFun_le_frobenius
    {n m : ℕ} (A : M n m (K_ℝ[K])) (i : Fin n) :
    ‖rowVectorOfFun (A i)‖ ≤ ‖A‖ := by
  change ‖WithLp.toLp 2 (A i)‖ ≤
    ‖WithLp.toLp 2 (fun r => WithLp.toLp 2 (A r))‖
  exact PiLp.norm_apply_le
    (x := (WithLp.toLp 2 (fun r => WithLp.toLp 2 (A r)) :
      PiLp 2 (fun _ : Fin n => PiLp 2 (fun _ : Fin m => K_ℝ[K])))) i

noncomputable def integralVectorEmbedding (m : ℕ) :
    (Fin m → 𝓞 K) →ₗ[ℤ] RowVector K m where
  toFun x := WithLp.toLp 2 (fun j => numberEmbedding K (x j : K))
  map_add' x y := by
    apply PiLp.ext
    intro j
    simp only [PiLp.toLp_apply, Pi.add_apply, map_add]
    exact numberEmbedding_add K (x j : K) (y j : K)
  map_smul' a x := by
    apply PiLp.ext
    intro j
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
  have hxy' : (integralVectorEmbedding (K := K) m x).ofLp =
      (integralVectorEmbedding (K := K) m y).ofLp := congrArg WithLp.ofLp hxy
  ext j
  apply numberEmbedding_injective K
  exact congrFun hxy' j

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

/- The paper fixes a lexicographic order by identifying `K_ℝ^m` with a
   finite real coordinate space (equation (1), lines 864--866 of the checked-in
   TeX).  `Finite.equivFin` records the fixed enumeration of the chosen
   integral-basis coordinates; transporting the usual lexicographic order on
   `Fin (Nat.card (Fin m × IntegralBasisIndex K)) → ℝ` gives the corresponding
   order on row vectors.  This is Lean infrastructure for the paper's order,
   not an additional mathematical hypothesis.
-/
noncomputable def rowVectorRealCoordinates (m : ℕ) :
    RowVector K m →ₗ[ℝ]
      (Fin (Nat.card (Fin m × IntegralBasisIndex K)) → ℝ) where
  toFun x i := realVectorCoordinates (K := K) m (fun j => x j)
    ((Finite.equivFin (Fin m × IntegralBasisIndex K)).symm i)
  map_add' x y := by
    funext i
    simp [realVectorCoordinates]
  map_smul' a x := by
    funext i
    simp [realVectorCoordinates]

theorem rowVectorRealCoordinates_injective (m : ℕ) :
    Function.Injective (rowVectorRealCoordinates (K := K) m) := by
  intro x y hxy
  apply (WithLp.linearEquiv 2 ℝ (Fin m → K_ℝ[K])).injective
  apply realVectorCoordinates_injective (K := K) m
  funext p
  have hp := congrFun hxy
    ((Finite.equivFin (Fin m × IntegralBasisIndex K)) p)
  simpa [rowVectorRealCoordinates] using hp

/- This instance is the formal version of the paper's fixed lexicographic
   tie-breaker.  `LinearOrder.lift'` is valid because the coordinate map above
   is injective. -/
noncomputable def rowVectorLexOrder {m : ℕ} :
    LinearOrder (RowVector K m) := by
  letI : LinearOrder
      (Fin (Nat.card (Fin m × IntegralBasisIndex K)) → ℝ) :=
    Pi.Lex.linearOrder
  exact LinearOrder.lift' (rowVectorRealCoordinates (K := K) m)
    (rowVectorRealCoordinates_injective (K := K) m)

noncomputable instance rowVectorLinearOrder {m : ℕ} :
    LinearOrder (RowVector K m) := rowVectorLexOrder (K := K)

noncomputable instance rowVectorSMulCommClass {m : ℕ} :
    SMulCommClass K ℝ (RowVector K m) where
  smul_comm c r x := by
    apply PiLp.ext
    intro j
    exact kReal_smul_comm_real K c r (x j)

noncomputable instance rowVectorKRealSMulCommClass {m : ℕ} :
    SMulCommClass K_ℝ[K] ℝ (RowVector K m) where
  smul_comm c r x := by
    apply PiLp.ext
    intro j
    exact kReal_smul_comm_real_all K c (x j) r

noncomputable instance rowVectorKRealIsScalarTower {m : ℕ} :
    IsScalarTower ℝ K_ℝ[K] (RowVector K m) where
  smul_assoc r c x := by
    apply PiLp.ext
    intro j
    exact kReal_smul_assoc_real K r c (x j)

/- `K_ℝ` is the real span of the Minkowski images of the integral basis of
   `𝓞_K`.  This is the coordinate form of the paper's fixed isomorphism
   `K_ℝ ≃ ℝ^d`, and is used only to prove that the real row span is stable
   under the `K_ℝ`-action. -/
theorem exists_real_combination_numberEmbedding (c : K_ℝ[K]) :
    ∃ a : IntegralBasisIndex K → ℝ,
      c = ∑ i, a i • numberEmbedding K
        ((NumberField.integralBasis K i : K)) := by
  let I := IntegralBasisIndex K
  letI : Fintype I := Fintype.ofFinite I
  let b := NumberField.mixedEmbedding.latticeBasis K
  let a : I → ℝ := fun i =>
    b.repr (NumberField.mixedEmbedding.euclidean.toMixed K c) i
  refine ⟨a, ?_⟩
  apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
  rw [map_sum]
  simp only [(NumberField.mixedEmbedding.euclidean.toMixed K).map_smul]
  rw [← b.sum_repr (NumberField.mixedEmbedding.euclidean.toMixed K c)]
  apply Finset.sum_congr rfl
  intro i hi
  simp [a, b, NumberField.mixedEmbedding.latticeBasis_apply, numberEmbedding]

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

/- [Lean infrastructure] The topology of `PiLp` is canonical, but the
   measurable-space instance is not inferred through the `RowVector`
   abbreviation reliably.  Fix the ambient Borel structure explicitly; the
   subspaces below then receive the induced subtype structure. -/
noncomputable local instance rowVectorMeasurableSpace {m : ℕ} :
    MeasurableSpace (RowVector K m) := borel (RowVector K m)

local instance rowVectorBorelSpace {m : ℕ} :
    BorelSpace (RowVector K m) := ⟨rfl⟩

/- The rational row space embedded coordinatewise in Minkowski space. -/
noncomputable def rowSpaceVectorEmbeddingQ {m k : ℕ}
    (V : Grassmannian K m k) :
    V.1 →ₗ[ℚ] RowVector K m where
  toFun x := WithLp.toLp 2 (fun j => numberEmbedding K (x.1 j))
  map_add' x y := by
    apply PiLp.ext
    intro j
    exact numberEmbedding_add K _ _
  map_smul' q x := by
    apply PiLp.ext
    intro j
    exact numberEmbedding_rat_smul K q (x.1 j)

@[simp]
theorem rowSpaceVectorEmbeddingQ_apply {m k : ℕ}
    (V : Grassmannian K m k) (x : V.1) (j : Fin m) :
    rowSpaceVectorEmbeddingQ V x j = numberEmbedding K (x.1 j) := rfl

/- [Derived consequence] The same coordinate embedding, now with the genuine
   `K`-action from `Foundations`.  This is useful for the separate rational
   `K`-span calculation below; the paper's successive minima use the
   `K_ℝ`-span, which is formalized through `rowRealSpan` instead. -/
noncomputable def rowSpaceVectorEmbeddingK {m k : ℕ}
    (V : Grassmannian K m k) :
    V.1 →ₗ[K] RowVector K m where
  toFun x := WithLp.toLp 2 (fun j => numberEmbedding K (x.1 j))
  map_add' x y := by
    apply PiLp.ext
    intro j
    exact numberEmbedding_add K _ _
  map_smul' c x := by
    apply PiLp.ext
    intro j
    change numberEmbedding K (c * x.1 j) =
      c • numberEmbedding K (x.1 j)
    change (numberEmbeddingRingHom K) (c * x.1 j) = _
    rw [map_mul, kReal_smul_eq_mul]
    simp only [numberEmbeddingRingHom_apply]

@[simp]
theorem rowSpaceVectorEmbeddingK_apply {m k : ℕ}
    (V : Grassmannian K m k) (x : V.1) (j : Fin m) :
    rowSpaceVectorEmbeddingK V x j = numberEmbedding K (x.1 j) := rfl

theorem rowSpaceVectorEmbeddingK_injective {m k : ℕ}
    (V : Grassmannian K m k) :
    Function.Injective (rowSpaceVectorEmbeddingK V) := by
  intro x y hxy
  apply Subtype.ext
  funext j
  apply numberEmbedding_injective K
  exact congrArg (fun z : RowVector K m => z j) hxy

noncomputable def embeddedIntegralRowModule {m k : ℕ}
    (V : Grassmannian K m k) : Submodule ℤ (RowVector K m) :=
  (integralRowModule V).restrictScalars ℤ |>.map
    (integralVectorEmbedding (K := K) m)

theorem mem_embeddedIntegralRowModule_iff {m k : ℕ}
    (V : Grassmannian K m k) (x : RowVector K m) :
    x ∈ embeddedIntegralRowModule V ↔
      ∃ v ∈ integralRowModule V,
        integralVectorEmbedding (K := K) m v = x := by
  rfl

/- The embedded integral row module is stable under multiplication by an
   algebraic integer.  This is the lattice-membership input for the
   sublattice generated by the selected successive minima. -/
theorem embeddedIntegralRowModule_smul_integral
    {m k : ℕ} (V : Grassmannian K m k) (a : 𝓞 K)
    {x : RowVector K m} (hx : x ∈ embeddedIntegralRowModule V) :
    numberEmbedding K (a : K) • x ∈ embeddedIntegralRowModule V := by
  obtain ⟨v, hv, rfl⟩ := (mem_embeddedIntegralRowModule_iff V x).1 hx
  let av : integralRowModule V :=
    ⟨a • v, (integralRowModule V).smul_mem a hv⟩
  refine (mem_embeddedIntegralRowModule_iff V _).2 ⟨av, ?_, ?_⟩
  · exact av.property
  · apply PiLp.ext
    intro j
    dsimp [av]
    simpa [Pi.smul_apply, smul_eq_mul] using
      (map_mul (numberEmbeddingRingHom K) (a : K) (v j : K))

/- [Derived consequence] The `K`-span of `Λ_D` is exactly the embedded rational
   row space.  This is a separate number-field `K`-span statement.  It is not
   the `K_ℝ`-span in Definition `de:defi_of_successive`, and is not used as a
   replacement for that construction. -/
theorem span_embeddedIntegralRowModule_eq_range_rowSpaceVectorEmbeddingK
    {m k : ℕ} (V : Grassmannian K m k) :
    Submodule.span K (embeddedIntegralRowModule V : Set (RowVector K m)) =
      LinearMap.range (rowSpaceVectorEmbeddingK V) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨v, hv, rfl⟩ :=
      (mem_embeddedIntegralRowModule_iff V x).1 hx
    refine ⟨integralRowToRowSpace V ⟨v, hv⟩, ?_⟩
    apply PiLp.ext
    intro j
    rfl
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    let W : Submodule K (RowVector K m) :=
      Submodule.span K (embeddedIntegralRowModule V : Set (RowVector K m))
    change rowSpaceVectorEmbeddingK V y ∈ W
    have hy : y ∈ Submodule.span ℚ
        (Set.range (fun v : integralRowModule V =>
          (integralRowToRowSpace V v : V.1))) := by
      rw [span_range_integralRowToRowSpace_rat V]
      trivial
    refine Submodule.span_induction
      (p := fun z : V.1 => fun _ => rowSpaceVectorEmbeddingK V z ∈ W)
      ?_ ?_ ?_ ?_ hy
    · intro z hz
      obtain ⟨v, rfl⟩ := hz
      have hvmap : rowSpaceVectorEmbeddingK V
          (integralRowToRowSpace V v) =
          integralVectorEmbedding (K := K) m v := by
        apply PiLp.ext
        intro j
        rfl
      rw [hvmap]
      apply Submodule.subset_span
      exact (mem_embeddedIntegralRowModule_iff V _).2
        ⟨v.1, v.2, rfl⟩
    · simpa using W.zero_mem
    · intro z z' _ _ hz hz'
      simpa using W.add_mem hz hz'
    · intro q z _ hz
      rw [← Rat.cast_smul_eq_qsmul K q z, map_smul]
      exact W.smul_mem (q : K) hz

theorem span_embeddedIntegralRowModule_finrank {m k : ℕ}
    (V : Grassmannian K m k) :
    Module.finrank K
        (Submodule.span K (embeddedIntegralRowModule V : Set (RowVector K m))) = k := by
  rw [span_embeddedIntegralRowModule_eq_range_rowSpaceVectorEmbeddingK V,
    LinearMap.finrank_range_of_inj (rowSpaceVectorEmbeddingK_injective V), V.2]

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
    exact (PiLp.continuous_apply 2 _ j).comp continuous_subtype_val
  · intro x y hxy
    apply Subtype.ext
    apply PiLp.ext
    intro j
    exact congrArg Subtype.val (congrFun hxy j)

/- The real subspace `Λ_D ⊗_ℤ ℝ`. -/
noncomputable def rowRealSpan {m k : ℕ} (V : Grassmannian K m k) :
    Submodule ℝ (RowVector K m) :=
  Submodule.span ℝ (embeddedIntegralRowModule V : Set (RowVector K m))

noncomputable local instance rowRealSpanMeasurableSpace {m k : ℕ}
    (V : Grassmannian K m k) : MeasurableSpace (rowRealSpan V) :=
  @Subtype.instMeasurableSpace (RowVector K m)
    (fun x => x ∈ rowRealSpan V) (rowVectorMeasurableSpace (K := K))

local instance rowRealSpanBorelSpace {m k : ℕ}
    (V : Grassmannian K m k) :
    @BorelSpace (rowRealSpan V) _ (rowRealSpanMeasurableSpace V) :=
  @Subtype.borelSpace (RowVector K m) _ (rowVectorMeasurableSpace (K := K))
    (rowVectorBorelSpace (K := K)) (fun x => x ∈ rowRealSpan V)

/- [Lean infrastructure] Naming the induced structures keeps typeclass search
   on the finite `PiLp` product from unfolding the submodule construction. -/
noncomputable local instance rowRealSpanNormedSpace {m k : ℕ}
    (V : Grassmannian K m k) : NormedSpace ℝ (rowRealSpan V) :=
  Submodule.normedSpace (rowRealSpan V)

noncomputable local instance rowRealSpanInnerProductSpace {m k : ℕ}
    (V : Grassmannian K m k) : InnerProductSpace ℝ (rowRealSpan V) :=
  Submodule.innerProductSpace (rowRealSpan V)

/- [Lean infrastructure] The coordinatewise Minkowski embedding of the
   rational row space K^m.  Its rational span is identified below with the
   ambient algebraic-integer module used by the paper's projection argument. -/
noncomputable def ambientRowEmbeddingQ (m : ℕ) :
    (Fin m → K) →ₗ[ℚ] RowVector K m where
  toFun x := rowVectorOfFun (fun j => numberEmbedding K (x j))
  map_add' x y := by
    apply PiLp.ext
    intro j
    simp [numberEmbedding_add]
  map_smul' q x := by
    apply PiLp.ext
    intro j
    change numberEmbedding K (q • x j) =
      (q : ℝ) • numberEmbedding K (x j)
    exact numberEmbedding_rat_smul K q (x j)

/- [Lean infrastructure] The ambient algebraic-integer row module in the
   Minkowski row space.  This is the product lattice whose projection is used
   in the proof of `le:low_rank_induction` (papers/katznelson.tex, lines
   1475--1479); it is the ambient version of the integral row vectors in
   `eq:defi_of_lambda` (lines 760--795). -/
noncomputable def ambientIntegralRowModule (m : ℕ) :
    Submodule ℤ (RowVector K m) where
  carrier := {x | ∀ j, x j ∈ NumberField.mixedEmbedding.euclidean.integerLattice K}
  zero_mem' := by
    intro j
    exact (NumberField.mixedEmbedding.euclidean.integerLattice K).zero_mem
  add_mem' := by
    intro x y hx hy j
    change x j + y j ∈ NumberField.mixedEmbedding.euclidean.integerLattice K
    exact (NumberField.mixedEmbedding.euclidean.integerLattice K).add_mem (hx j) (hy j)
  smul_mem' := by
    intro a x hx j
    change a • x j ∈ NumberField.mixedEmbedding.euclidean.integerLattice K
    exact (NumberField.mixedEmbedding.euclidean.integerLattice K).smul_mem a (hx j)

@[simp]
theorem ambientIntegralRowModule_mem_iff (m : ℕ) (x : RowVector K m) :
    x ∈ ambientIntegralRowModule (K := K) m ↔
      ∀ j, x j ∈ NumberField.mixedEmbedding.euclidean.integerLattice K := Iff.rfl

/- [derived consequence, paper `le:low_rank_induction`, lines 1447--1453]
   Every embedded vector with algebraic-integer coordinates belongs to the
   ambient product lattice used in the projection argument. -/
theorem integralVectorEmbedding_mem_ambientIntegralRowModule
    (m : ℕ) (x : Fin m → 𝓞 K) :
    integralVectorEmbedding (K := K) m x ∈
      ambientIntegralRowModule (K := K) m := by
  rw [ambientIntegralRowModule_mem_iff]
  intro j
  rw [integralVectorEmbedding_apply]
  rw [NumberField.mixedEmbedding.euclidean.integerLattice]
  change NumberField.mixedEmbedding.euclidean.toMixed K
      (numberEmbedding K (x j : K)) ∈
    NumberField.mixedEmbedding.integerLattice K
  simp [numberEmbedding]

/- [derived consequence, paper `le:low_rank_induction`, lines 1447--1479]
   The ambient algebraic-integer row module is exactly the image of the
   coordinatewise integral embedding.  This makes the integral kernel of the
   projection explicit, rather than only identifying its rational span. -/
theorem ambientIntegralRowModule_mem_iff_exists_integralVector
    (m : ℕ) (x : RowVector K m) :
    x ∈ ambientIntegralRowModule (K := K) m ↔
      ∃ a : Fin m → 𝓞 K, integralVectorEmbedding (K := K) m a = x := by
  constructor
  · intro hx
    rw [ambientIntegralRowModule_mem_iff] at hx
    choose a ha using fun j =>
      (show ∃ a : 𝓞 K, numberEmbedding K (a : K) = x j from by
        rw [NumberField.mixedEmbedding.euclidean.integerLattice] at hx
        have hj := hx j
        change NumberField.mixedEmbedding.euclidean.toMixed K (x j) ∈
          NumberField.mixedEmbedding.integerLattice K at hj
        rw [NumberField.mixedEmbedding.integerLattice] at hj
        obtain ⟨a, ha⟩ := hj
        refine ⟨a, ?_⟩
        apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
        simpa [numberEmbedding] using ha)
    refine ⟨a, ?_⟩
    apply PiLp.ext
    intro j
    change numberEmbedding K (a j : K) = x j
    exact ha j
  · rintro ⟨a, rfl⟩
    exact integralVectorEmbedding_mem_ambientIntegralRowModule (K := K) m a

noncomputable instance ambientIntegralRowModule.discreteTopology (m : ℕ) :
    DiscreteTopology (ambientIntegralRowModule (K := K) m) := by
  let L := NumberField.mixedEmbedding.euclidean.integerLattice K
  let _ : DiscreteTopology L := by
    dsimp [L]
    infer_instance
  let toProduct : ambientIntegralRowModule (K := K) m → (Fin m → L) :=
    fun x j => ⟨x.1 j, by
      exact (ambientIntegralRowModule_mem_iff m x.1).mp x.2 j⟩
  apply DiscreteTopology.of_continuous_injective (f := toProduct)
  · apply continuous_pi
    intro j
    apply Continuous.subtype_mk
    exact (PiLp.continuous_apply 2 _ j).comp continuous_subtype_val
  · intro x y hxy
    apply Subtype.ext
    apply PiLp.ext
    intro j
    exact congrArg Subtype.val (congrFun hxy j)

/- [derived consequence] The ambient product module spans the full Minkowski
   row space.  This is the ambient rank part of the projected-lattice claim
   used in `le:low_rank_induction` (papers/katznelson.tex, lines 1475--1479).
   It does not establish the projected module's discreteness or covolume. -/
theorem ambientIntegralRowModule_span_top (m : ℕ) :
    Submodule.span ℝ
      (ambientIntegralRowModule (K := K) m : Set (RowVector K m)) = ⊤ := by
  let L := NumberField.mixedEmbedding.euclidean.integerLattice K
  let S : Submodule ℝ (RowVector K m) :=
    Submodule.span ℝ
      (ambientIntegralRowModule (K := K) m : Set (RowVector K m))
  have hcoord : ∀ (j : Fin m) (x : KReal K),
      x ∈ Submodule.span ℝ (L : Set (KReal K)) →
        PiLp.single 2 j x ∈ S := by
    intro j x hx
    refine Submodule.span_induction (p := fun y _ =>
      PiLp.single 2 j y ∈ S) ?_ ?_ ?_ ?_ hx
    · intro y hy
      apply Submodule.subset_span
      apply (ambientIntegralRowModule_mem_iff m _).2
      intro i
      by_cases hij : i = j
      · subst i
        simpa [PiLp.single_apply] using hy
      · simp [PiLp.single_apply, hij]
    · have hzero : (PiLp.single 2 j (0 : KReal K) : RowVector K m) = 0 := by
        apply PiLp.ext
        intro i
        simp [PiLp.single_apply]
      rw [hzero]
      exact S.zero_mem
    · intro y z _ _ hy hz
      simpa [PiLp.single_add] using S.add_mem hy hz
    · intro a y _ hy
      have hsmul : (PiLp.single 2 j (a • y) : RowVector K m) =
          a • (PiLp.single 2 j y : RowVector K m) := by
        apply PiLp.ext
        intro i
        simp [PiLp.single_apply]
      rw [hsmul]
      exact S.smul_mem a hy
  rw [eq_top_iff]
  intro x _
  have hdecomp : x = ∑ j, PiLp.single 2 j (x j) := by
    apply PiLp.ext
    intro j
    simp [PiLp.single_apply]
  rw [hdecomp]
  apply S.sum_mem
  intro j _
  apply hcoord j (x j)
  have hspan : Submodule.span ℝ
      (NumberField.mixedEmbedding.euclidean.integerLattice K : Set (KReal K)) = ⊤ :=
    IsZLattice.span_top (K := ℝ)
      (L := NumberField.mixedEmbedding.euclidean.integerLattice K)
  rw [hspan]
  trivial

noncomputable instance ambientIntegralRowModule.isZLattice (m : ℕ) :
    IsZLattice ℝ (ambientIntegralRowModule (K := K) m) := by
  exact ⟨ambientIntegralRowModule_span_top m⟩

/- [paper, `le:domain_dimension_bound`, lines 1558--1568]
   The ambient algebraic-integer row module has the expected real rank
   `m * degree K`.  This is the dimension input for the ambient lattice
   p-series used in the noncritical radius-sum estimate. -/
theorem ambientIntegralRowModule_finrank (m : ℕ) :
    Module.finrank ℤ (ambientIntegralRowModule (K := K) m) =
      m * degree K := by
  rw [ZLattice.rank (K := ℝ)
    (ambientIntegralRowModule (K := K) m), rowVector_finrank]

/- [paper, `le:domain_dimension_bound`, lines 1558--1568]
   Consequently, inverse norm powers above the ambient dimension are
   summable.  This is the ambient-lattice form of the shell estimate used in
   the noncritical part of the radius sum; no dyadic decomposition is added. -/
theorem summable_ambientIntegralRowModule_norm_inv_pow
    {m q : ℕ} (hgap : m * degree K < q) :
    Summable (fun v : ambientIntegralRowModule (K := K) m =>
      ‖(v : RowVector K m)‖⁻¹ ^ q) := by
  apply ZLattice.summable_norm_pow_inv
    (ambientIntegralRowModule (K := K) m)
  simpa [ambientIntegralRowModule_finrank] using hgap

/- [derived consequence of paper `le:domain_dimension_bound`, lines
   1558--1568] In the noncritical radius-sum range, the exponent appearing in
   the innermost row sum is strictly above the ambient real dimension.  This
   is only a convenient specialization of the preceding p-series theorem; it
   does not introduce a dyadic decomposition or replace the manuscript's
   nested sum. -/
theorem summable_ambientIntegralRowModule_norm_inv_pow_of_noncritical
    {m n : ℕ} (hgap : 1 < (n - m) * degree K) :
    Summable (fun v : ambientIntegralRowModule (K := K) m =>
      ‖(v : RowVector K m)‖⁻¹ ^ (n * degree K - 1)) := by
  have hgap' := hgap
  rw [Nat.sub_mul] at hgap'
  apply summable_ambientIntegralRowModule_norm_inv_pow
  omega

/- [derived consequence, paper le:low_rank_induction, lines 1475--1479]
   The rational span of the ambient algebraic-integer module is precisely the
   Minkowski image of K^m.  The forward inclusion uses the defining
   coordinatewise integer lattice; the reverse inclusion expands each
   coordinate in the manuscript's integral basis of K/ℚ. -/
theorem ambientIntegralRowModule_ratSpan_eq_range (m : ℕ) :
    Submodule.span ℚ
        (ambientIntegralRowModule (K := K) m : Set (RowVector K m)) =
      LinearMap.range (ambientRowEmbeddingQ (K := K) m) := by
  let S : Submodule ℚ (RowVector K m) :=
    Submodule.span ℚ
      (ambientIntegralRowModule (K := K) m : Set (RowVector K m))
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨a, ha⟩ : ∃ a : Fin m → 𝓞 K, ∀ j,
        numberEmbedding K (a j : K) = x j := by
      choose a ha using fun j =>
        (show ∃ a : 𝓞 K, numberEmbedding K (a : K) = x j from by
          exact (by
            change x ∈ ambientIntegralRowModule (K := K) m at hx
            rw [ambientIntegralRowModule_mem_iff] at hx
            rw [NumberField.mixedEmbedding.euclidean.integerLattice] at hx
            have hj := hx j
            change NumberField.mixedEmbedding.euclidean.toMixed K (x j) ∈
              NumberField.mixedEmbedding.integerLattice K at hj
            rw [NumberField.mixedEmbedding.integerLattice] at hj
            obtain ⟨a, ha⟩ := hj
            refine ⟨a, ?_⟩
            apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
            simpa [numberEmbedding] using ha))
      exact ⟨a, ha⟩
    refine ⟨fun j => (a j : K), ?_⟩
    apply PiLp.ext
    intro j
    change numberEmbedding K (a j : K) = x j
    exact ha j
  · intro x hx
    obtain ⟨w, rfl⟩ := hx
    let S : Submodule ℚ (RowVector K m) :=
      Submodule.span ℚ
        (ambientIntegralRowModule (K := K) m : Set (RowVector K m))
    have hbasis (i : IntegralBasisIndex K) :
        numberEmbedding K (NumberField.integralBasis K i) ∈
          NumberField.mixedEmbedding.euclidean.integerLattice K := by
      rw [NumberField.mixedEmbedding.euclidean.integerLattice]
      change NumberField.mixedEmbedding K (NumberField.integralBasis K i) ∈
        NumberField.mixedEmbedding.integerLattice K
      rw [← NumberField.mixedEmbedding.latticeBasis_apply K i]
      rw [← NumberField.mixedEmbedding.span_latticeBasis K]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hsingle (j : Fin m) (i : IntegralBasisIndex K) :
        (PiLp.single 2 j (numberEmbedding K
          (NumberField.integralBasis K i)) : RowVector K m) ∈ S := by
      apply Submodule.subset_span
      change (PiLp.single 2 j (numberEmbedding K
        (NumberField.integralBasis K i)) : RowVector K m) ∈
        ambientIntegralRowModule (K := K) m
      rw [ambientIntegralRowModule_mem_iff]
      intro h
      by_cases hji : h = j
      · subst h
        simpa using hbasis i
      · simp [PiLp.single_apply, hji]
    have hcoord (j : Fin m) :
        (PiLp.single 2 j (numberEmbedding K (w j)) : RowVector K m) ∈ S := by
      rw [← Basis.sum_repr (NumberField.integralBasis K) (w j)]
      have hsingle_sum :
          (PiLp.single 2 j (numberEmbedding K
            (∑ i, ((NumberField.integralBasis K).repr (w j)) i •
              (NumberField.integralBasis K i))) : RowVector K m) =
            ∑ i, ((NumberField.integralBasis K).repr (w j) i) •
              (PiLp.single 2 j (numberEmbedding K
                (NumberField.integralBasis K i)) : RowVector K m) := by
        apply PiLp.ext
        intro h
        by_cases hji : h = j
        · subst h
          simp only [WithLp.ofLp_sum, WithLp.ofLp_smul,
            PiLp.ofLp_single, Pi.single_eq_same, Finset.sum_apply,
            Pi.smul_apply]
          change (numberEmbeddingRingHom K)
              (∑ i, ((NumberField.integralBasis K).repr (w j)) i •
                (NumberField.integralBasis K i)) = _
          rw [map_sum]
          simp_rw [map_rat_smul, numberEmbeddingRingHom_apply]
        · simp [PiLp.single_apply, hji]
      rw [hsingle_sum]
      apply Submodule.sum_mem
      intro i hi
      exact S.smul_mem ((NumberField.integralBasis K).repr (w j) i)
        (hsingle j i)
    have hdecomp :
        rowVectorOfFun (fun j => numberEmbedding K (w j)) =
          ∑ j, PiLp.single 2 j (numberEmbedding K (w j)) := by
      apply PiLp.ext
      intro j
      simp [PiLp.single_apply]
    change rowVectorOfFun (fun j => numberEmbedding K (w j)) ∈ S
    rw [hdecomp]
    apply Submodule.sum_mem
    intro j hj
    exact hcoord j

/- [Lean infrastructure] This is the orthogonal projection of the ambient
   product lattice into the orthogonal complement of the row span.  The paper
   uses this projection in `le:low_rank_induction` (papers/katznelson.tex,
   lines 1475--1479), but does not package it as a named Lean object.  No
   discreteness or covolume assertion is made here. -/
noncomputable def projectedAmbientRowMap {m l : ℕ}
    (V : Grassmannian K m l) :
    RowVector K m →ₗ[ℤ] (rowRealSpan V)ᗮ :=
  ((rowRealSpan V)ᗮ.orthogonalProjectionOnto).toLinearMap.restrictScalars ℤ

noncomputable def projectedAmbientRowModule {m l : ℕ}
    (V : Grassmannian K m l) :
    Submodule ℤ ((rowRealSpan V)ᗮ) :=
  (ambientIntegralRowModule (K := K) m).map (projectedAmbientRowMap V)

/- [derived consequence, paper `le:low_rank_induction`, lines 1477--1479]
   The kernel of the orthogonal projection is the lower row space itself.
   This is the real-linear half of the primitive projected-lattice argument. -/
theorem projectedAmbientRowMap_eq_zero_iff_mem_rowRealSpan
    {m l : ℕ} (V : Grassmannian K m l) (x : RowVector K m) :
    projectedAmbientRowMap V x = 0 ↔ x ∈ rowRealSpan V := by
  change (rowRealSpan V)ᗮ.orthogonalProjectionOnto x = 0 ↔
    x ∈ rowRealSpan V
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff,
    Submodule.orthogonal_orthogonal_eq_closure]
  rw [(Submodule.closed_of_finiteDimensional
    (rowRealSpan V)).submodule_topologicalClosure_eq]

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   The projected module is finitely generated as a `ℤ`-module because it is
   the image of the ambient algebraic-integer module.  The discrete-topology
   part of the projected-lattice claim is proved below from its rational and
   real ranks. -/
noncomputable instance projectedAmbientRowModule.module_finite
    {m l : ℕ} (V : Grassmannian K m l) :
    Module.Finite ℤ (projectedAmbientRowModule (K := K) V) := by
  letI : Module.Finite ℤ (ambientIntegralRowModule (K := K) m) :=
    ZLattice.module_finite ℝ (ambientIntegralRowModule (K := K) m)
  exact Module.Finite.map (ambientIntegralRowModule (K := K) m)
    (projectedAmbientRowMap V)

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   The projection of an ambient integral row is an element of the projected
   ambient module by the definition of `Submodule.map`. -/
theorem projectedAmbientRowMap_mem_projectedAmbientRowModule
    {m l : ℕ} (V : Grassmannian K m l) {x : RowVector K m}
    (hx : x ∈ ambientIntegralRowModule (K := K) m) :
    projectedAmbientRowMap V x ∈
      projectedAmbientRowModule (K := K) V := by
  exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

/- [derived consequence] The real span of the projected ambient module is the
   whole orthogonal complement.  This proves the fullness part of the
   projected-lattice claim in `le:low_rank_induction`
   (papers/katznelson.tex, lines 1475--1479); the exact covolume identity
   `H(D')⁻¹` remains to be proved. -/
theorem projectedAmbientRowModule_span_top {m l : ℕ}
    (V : Grassmannian K m l) :
    Submodule.span ℝ
      (projectedAmbientRowModule (K := K) V : Set ((rowRealSpan V)ᗮ)) = ⊤ := by
  let L : Submodule ℤ (RowVector K m) :=
    ambientIntegralRowModule (K := K) m
  let P : RowVector K m →ₗ[ℝ] (rowRealSpan V)ᗮ :=
    ((rowRealSpan V)ᗮ.orthogonalProjectionOnto).toLinearMap
  let S : Submodule ℝ ((rowRealSpan V)ᗮ) :=
    Submodule.span ℝ
      (projectedAmbientRowModule (K := K) V : Set ((rowRealSpan V)ᗮ))
  have hP : ∀ x : RowVector K m,
      x ∈ Submodule.span ℝ (L : Set (RowVector K m)) → P x ∈ S := by
    intro x hx
    refine Submodule.span_induction (p := fun y _ => P y ∈ S) ?_ ?_ ?_ ?_ hx
    · intro y hy
      apply Submodule.subset_span
      exact ⟨y, hy, rfl⟩
    · simpa [P] using S.zero_mem
    · intro y z _ _ hy hz
      simpa [P, map_add] using S.add_mem hy hz
    · intro a y _ hy
      simpa [P, map_smul] using S.smul_mem a hy
  rw [eq_top_iff]
  intro x _
  have hxL : (x : RowVector K m) ∈
      Submodule.span ℝ (L : Set (RowVector K m)) := by
    rw [ambientIntegralRowModule_span_top]
    trivial
  have hPx : P (x : RowVector K m) ∈ S := hP _ hxL
  have hproj : P (x : RowVector K m) = x := by
    change (rowRealSpan V)ᗮ.orthogonalProjectionOnto (x : RowVector K m) = x
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x
  rw [← hproj]
  exact hPx

/- [Lean infrastructure] The standard `PiLp` norm and inner product are
   definitionally compatible with one another, but typeclass search does not
   reliably expose both through the dependent row-span family.  These named
   local instances keep the canonical structures explicit. -/
noncomputable local instance rowProductNormedSpace {m k n : ℕ}
    (V : Grassmannian K m k) :
    NormedSpace ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V)) :=
  PiLp.normedSpace (p := 2) ℝ _

noncomputable local instance rowProductInnerProductSpace {m k n : ℕ}
    (V : Grassmannian K m k) :
    InnerProductSpace ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V)) :=
  PiLp.innerProductSpace _

/- `PiLp` has the canonical finite-dimensional Euclidean measure, but the
   corresponding `MeasureSpace` instance is not synthesized in this
   dependent product situation.  Use the canonical Mathlib instance
   explicitly. -/
noncomputable local instance rowProductMeasureSpace {m k n : ℕ}
    (V : Grassmannian K m k) :
    MeasureTheory.MeasureSpace
      (PiLp 2 (fun _ : Fin n => rowRealSpan V)) :=
  measureSpaceOfInnerProductSpace

/- A rational basis of the row space gives a convenient basis for the real
   span after the Minkowski embedding. -/
abbrev RowSpaceBasisIndex {m k : ℕ} (V : Grassmannian K m k) :=
  Module.Free.ChooseBasisIndex ℚ V.1

noncomputable def rowSpaceBasisQ {m k : ℕ} (V : Grassmannian K m k) :
    Basis (RowSpaceBasisIndex V) ℚ V.1 :=
  Module.Free.chooseBasis ℚ V.1

noncomputable def embeddedRowBasisQ {m k : ℕ}
    (V : Grassmannian K m k) (i : RowSpaceBasisIndex V) :
    RowVector K m :=
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
  have hLI : LinearIndependent ℝ
      (fun i : RowSpaceBasisIndex V =>
        (fun j => numberEmbedding K ((rowSpaceBasisQ V i : V.1).1 j))) :=
    linearIndependent_numberEmbedding hsub
  let toLp : (Fin m → K_ℝ[K]) →ₗ[ℝ] RowVector K m :=
    (WithLp.linearEquiv 2 ℝ (Fin m → K_ℝ[K])).symm.toLinearMap
  have hker : LinearMap.ker toLp = ⊥ :=
    LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ
      (Fin m → K_ℝ[K])).symm.injective
  change LinearIndependent ℝ
    (fun i : RowSpaceBasisIndex V => rowSpaceVectorEmbeddingQ V
      (rowSpaceBasisQ V i))
  simpa [rowSpaceVectorEmbeddingQ, toLp, Function.comp_def] using
    hLI.map' toLp hker

theorem rowSpaceVectorEmbeddingQ_mem_rowRealSpan_of_mem_ratSpan
    {m k : ℕ} (V : Grassmannian K m k) (x : V.1)
    (hx : x ∈ Submodule.span ℚ
      (Set.range (fun v : integralRowModule V =>
        (integralRowToRowSpace V v : V.1)))) :
    rowSpaceVectorEmbeddingQ V x ∈ rowRealSpan V := by
  let W : Submodule ℚ (RowVector K m) :=
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
    obtain ⟨v, hv, hvy⟩ :=
      (mem_embeddedIntegralRowModule_iff V y).1 hy
    rw [← hvy]
    let x : V.1 := integralRowToRowSpace V ⟨v, hv⟩
    exact rowSpaceVectorEmbeddingQ_mem_span_embeddedRowBasisQ V x
  · rw [Submodule.span_le]
    intro y hy
    obtain ⟨i, rfl⟩ := hy
    apply rowSpaceVectorEmbeddingQ_mem_rowRealSpan_of_mem_ratSpan V
    rw [span_range_integralRowToRowSpace_rat V]
    trivial

/- [derived consequence, used in the paper step `le:low_rank_induction`,
   lines 1455--1477]  The Minkowski image of an algebraic K-row vector can
   lie in the real span of the lower row space only when the row vector itself
   lies in that K-row space.  This is the rational-basis/linear-independence
   bridge implicit when the paper passes from equal projected vectors to equal
   quotient classes. -/
set_option maxHeartbeats 1200000 in
theorem rowRealSpan_mem_ambient_to_mem
    {m k : ℕ} (V : Grassmannian K m k) (w : Fin m → K)
    (hw : rowVectorOfFun (fun j => numberEmbedding K (w j)) ∈
      rowRealSpan V) :
    w ∈ V.1 := by
  by_contra hwV
  letI : Module.Finite ℚ V.1 := FiniteDimensional.trans ℚ K V.1
  letI : Fintype (RowSpaceBasisIndex V) := Fintype.ofFinite _
  let b := rowSpaceBasisQ V
  let u : RowSpaceBasisIndex V → (Fin m → K) :=
    fun i => (b i : V.1).1
  have hu : LinearIndependent ℚ u := by
    exact b.linearIndependent.map'
      (V.1.subtype.restrictScalars ℚ)
      (LinearMap.ker_eq_bot.mpr V.1.subtype_injective)
  have hspan : Submodule.span ℚ (Set.range u) ≤
      V.1.restrictScalars ℚ := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    exact (b i).property
  have hw_not_mem : w ∉ Submodule.span ℚ (Set.range u) := by
    intro h
    exact hwV (hspan h)
  have huw : LinearIndependent ℚ
      (fun o : Option (RowSpaceBasisIndex V) =>
        Option.casesOn' o w u) :=
    hu.option hw_not_mem
  have h_embed_uw : LinearIndependent ℝ
      (fun o : Option (RowSpaceBasisIndex V) => fun j : Fin m =>
        numberEmbedding K ((Option.casesOn' o w u) j)) :=
    linearIndependent_numberEmbedding huw
  have h_embed_not_mem :
      (fun j => numberEmbedding K (w j)) ∉
        Submodule.span ℝ (Set.range (fun i =>
          (fun j => numberEmbedding K (u i j)))) := by
    have h_option_fun : LinearIndependent ℝ
        (fun o : Option (RowSpaceBasisIndex V) =>
          Option.casesOn' o
            (fun j => numberEmbedding K (w j))
            (fun i j => numberEmbedding K (u i j))) := by
      convert h_embed_uw using 1
      funext o j
      cases o <;> rfl
    exact (linearIndependent_option'.mp h_option_fun).2
  apply h_embed_not_mem
  have hrow : rowVectorOfFun (fun j => numberEmbedding K (w j)) ∈
      Submodule.span ℝ (Set.range (fun i =>
        rowVectorOfFun (fun j => numberEmbedding K (u i j)))) := by
    rw [rowRealSpan_eq_span_embeddedRowBasisQ V] at hw
    have hpoint : embeddedRowBasisQ V = (fun i =>
        rowVectorOfFun (fun j => numberEmbedding K (u i j))) := by
      funext i
      apply PiLp.ext
      intro j
      rfl
    rw [hpoint] at hw
    exact hw
  let ofLp : RowVector K m →ₗ[ℝ] (Fin m → K_ℝ[K]) :=
    (WithLp.linearEquiv 2 ℝ (Fin m → K_ℝ[K])).toLinearMap
  have hmap := Submodule.mem_map_of_mem (f := ofLp) hrow
  have himage : ofLp '' Set.range (fun i =>
        rowVectorOfFun (fun j => numberEmbedding K (u i j))) =
      Set.range (fun i => fun j => numberEmbedding K (u i j)) := by
    ext z
    constructor
    · rintro ⟨z', ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by funext j; rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨rowVectorOfFun (fun j => numberEmbedding K (u i j)),
        ⟨i, rfl⟩, by funext j; rfl⟩
  rw [Submodule.map_span, himage] at hmap
  exact hmap

/- [derived consequence, used in the paper step `le:low_rank_induction`,
   lines 1455--1477]  Specialize the preceding intersection statement to the
   integral vectors used by the manuscript.  The displayed subtraction is
   retained in the paper's coordinatewise notation. -/
theorem rowRealSpan_mem_integral_difference_to_mem
    {m k : ℕ} (V : Grassmannian K m k)
    (x y : Fin m → 𝓞 K)
    (hxy : integralVectorEmbedding (K := K) m x -
        integralVectorEmbedding (K := K) m y ∈ rowRealSpan V) :
    (fun j : Fin m => (x j : K)) - (fun j : Fin m => (y j : K)) ∈ V.1 := by
  apply rowRealSpan_mem_ambient_to_mem V
    (fun j : Fin m => (x j : K) - (y j : K))
  have heq : rowVectorOfFun (fun j =>
      numberEmbedding K ((x j : K) - (y j : K))) =
      integralVectorEmbedding (K := K) m x -
        integralVectorEmbedding (K := K) m y := by
    apply PiLp.ext
    intro j
    change numberEmbedding K ((x j : K) - (y j : K)) =
      numberEmbedding K (x j : K) - numberEmbedding K (y j : K)
    change (numberEmbeddingRingHom K) ((x j : K) - (y j : K)) = _
    exact map_sub (numberEmbeddingRingHom K) (x j : K) (y j : K)
  rw [heq]
  exact hxy

/- [derived consequence, paper `le:low_rank_induction`, lines 1447--1479]
   Inside the ambient algebraic-integer row lattice, the vectors lying in the
   real row span are precisely the primitive integral row module
   `Λ_{D'}`.  This is the lattice-intersection statement used by the
   projection argument. -/
theorem embeddedIntegralRowModule_eq_ambient_inf_rowRealSpan
    {m k : ℕ} (V : Grassmannian K m k) :
    embeddedIntegralRowModule V =
      ambientIntegralRowModule (K := K) m ⊓
        (rowRealSpan V).restrictScalars ℤ := by
  ext x
  constructor
  · intro hx
    constructor
    · obtain ⟨v, hv, rfl⟩ := (mem_embeddedIntegralRowModule_iff V x).1 hx
      exact integralVectorEmbedding_mem_ambientIntegralRowModule (K := K) m v
    · change x ∈ rowRealSpan V
      exact Submodule.subset_span hx
  · rintro ⟨hxambient, hxrow⟩
    change x ∈ rowRealSpan V at hxrow
    obtain ⟨a, ha⟩ :=
      (ambientIntegralRowModule_mem_iff_exists_integralVector (K := K) m x).1
        hxambient
    have ha_row : integralVectorEmbedding (K := K) m a ∈ rowRealSpan V := by
      rw [ha]
      exact hxrow
    have ha_mem : (fun j => (a j : K)) ∈ V.1 := by
      apply rowRealSpan_mem_ambient_to_mem V (fun j => (a j : K))
      change integralVectorEmbedding (K := K) m a ∈ rowRealSpan V
      exact ha_row
    let aV : integralRowModule V := ⟨a, ha_mem⟩
    refine (mem_embeddedIntegralRowModule_iff V x).2 ⟨aV, aV.property, ?_⟩
    simpa [aV] using ha

/- [derived consequence, paper `le:low_rank_induction`, lines 1477--1479]
   The integral kernel of the projection of `𝓞_K^m` is exactly
   `Λ_{D'}`.  This combines the preceding projection-kernel fact with the
   proved ambient/intersection identification. -/
theorem ambientIntegralRowModule_inf_kernel_projectedAmbientRowMap_eq
    {m l : ℕ} (V : Grassmannian K m l) :
    ambientIntegralRowModule (K := K) m ⊓
      LinearMap.ker (projectedAmbientRowMap V) =
      embeddedIntegralRowModule V := by
  rw [embeddedIntegralRowModule_eq_ambient_inf_rowRealSpan V]
  ext x
  change (x ∈ ambientIntegralRowModule (K := K) m ∧
      projectedAmbientRowMap V x = 0) ↔
    (x ∈ ambientIntegralRowModule (K := K) m ∧ x ∈ rowRealSpan V)
  rw [projectedAmbientRowMap_eq_zero_iff_mem_rowRealSpan]

/- [derived consequence, paper `le:low_rank_induction`, lines 1477--1479]
   `Λ_{D'}` is saturated in the ambient integral row lattice.  Equivalently,
   an integral row whose nonzero integral multiple belongs to the lower row
   lattice already belongs to it.  This is the primitivity condition needed
   for the standard projection-covolume identity. -/
theorem embeddedIntegralRowModule_saturated_in_ambient
    {m l : ℕ} (V : Grassmannian K m l) {a : ℤ} (ha : a ≠ 0)
    {x : RowVector K m}
    (hxambient : x ∈ ambientIntegralRowModule (K := K) m)
    (hax : a • x ∈ embeddedIntegralRowModule V) :
    x ∈ embeddedIntegralRowModule V := by
  rw [← ambientIntegralRowModule_inf_kernel_projectedAmbientRowMap_eq V] at hax ⊢
  refine ⟨hxambient, ?_⟩
  change projectedAmbientRowMap V x = 0
  have hzero : projectedAmbientRowMap V (a • x) = 0 := hax.2
  rw [(projectedAmbientRowMap V).map_smul] at hzero
  have haR : (a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hzeroR : (a : ℝ) • projectedAmbientRowMap V x = 0 := by
    simpa only [Int.cast_smul_eq_zsmul] using hzero
  exact (smul_eq_zero.mp hzeroR).resolve_left haR

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  Put the projection kernel inside the ambient integral module,
   so that its quotient is an ordinary `ℤ`-module.  This is only a change of
   carrier: its image in the Minkowski row space is the already named
   `Λ_{D'}`. -/
noncomputable def ambientKernelSubmodule {m l : ℕ}
    (V : Grassmannian K m l) :
    Submodule ℤ (ambientIntegralRowModule (K := K) m) :=
  (embeddedIntegralRowModule V).comap
    (ambientIntegralRowModule (K := K) m).subtype

/- [derived consequence, paper `le:low_rank_induction`, lines 1477--1479]
   Membership in the kernel regarded inside the ambient lattice is exactly
   membership in `Λ_{D'}` after forgetting the ambient subtype. -/
theorem mem_ambientKernelSubmodule_iff
    {m l : ℕ} (V : Grassmannian K m l)
    (x : ambientIntegralRowModule (K := K) m) :
    x ∈ ambientKernelSubmodule (K := K) V ↔
      (x : RowVector K m) ∈ embeddedIntegralRowModule V := Iff.rfl

/- [derived consequence, paper `le:low_rank_induction`, lines 1477--1479]
   The ambient-carrier version of primitivity: the kernel submodule is
   saturated, hence its quotient has no integral torsion. -/
theorem ambientKernelSubmodule_saturated
    {m l : ℕ} (V : Grassmannian K m l) {a : ℤ} (ha : a ≠ 0)
    {x : ambientIntegralRowModule (K := K) m}
    (hax : a • x ∈ ambientKernelSubmodule (K := K) V) :
    x ∈ ambientKernelSubmodule (K := K) V := by
  rw [mem_ambientKernelSubmodule_iff] at hax ⊢
  apply embeddedIntegralRowModule_saturated_in_ambient V ha x.property
  simpa using hax

/- [derived consequence, paper `le:low_rank_induction`, lines 1477--1479]
   The quotient of the ambient integral lattice by `Λ_{D'}` is torsion-free.
   This is the algebraic content of the paper's use of a primitive sublattice,
   and will supply a genuine integral splitting for the covolume calculation.
   No quotient-freeness is assumed. -/
noncomputable instance ambientKernelQuotient.isTorsionFree
    {m l : ℕ} (V : Grassmannian K m l) :
    Module.IsTorsionFree ℤ
      ((ambientIntegralRowModule (K := K) m) ⧸
        ambientKernelSubmodule (K := K) V) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro a q haq
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    obtain ⟨x, rfl⟩ :=
      (ambientKernelSubmodule (K := K) V).mkQ_surjective q
    change a • (Submodule.Quotient.mk x :
      (ambientIntegralRowModule (K := K) m) ⧸
        ambientKernelSubmodule (K := K) V) = 0 at haq
    rw [← Submodule.Quotient.mk_smul] at haq
    have hmem : a • x ∈ ambientKernelSubmodule (K := K) V :=
      (Submodule.Quotient.mk_eq_zero _).mp haq
    change (Submodule.Quotient.mk x :
      (ambientIntegralRowModule (K := K) m) ⧸
        ambientKernelSubmodule (K := K) V) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (ambientKernelSubmodule_saturated V ha hmem)

/- [derived consequence, paper `le:low_rank_induction`, lines 1477--1479]
   Since the quotient is both finitely generated and torsion-free over the
   PID `ℤ`, it is free.  The instance is obtained from Mathlib's verified
   PID theorem, not postulated as an external lattice fact. -/
noncomputable instance ambientKernelQuotient.moduleFree
    {m l : ℕ} (V : Grassmannian K m l) :
    Module.Free ℤ
      ((ambientIntegralRowModule (K := K) m) ⧸
        ambientKernelSubmodule (K := K) V) := by
  infer_instance

/- [derived consequence, paper `le:low_rank_induction`, lines 1477--1479]
   Choose the integral splitting furnished by the preceding freeness result.
   Its defining identity is recorded immediately below, so later determinant
   calculations use a proved section rather than an unspecified complement. -/
noncomputable def ambientKernelQuotientSection {m l : ℕ}
    (V : Grassmannian K m l) :
    ((ambientIntegralRowModule (K := K) m) ⧸
      ambientKernelSubmodule (K := K) V) →ₗ[ℤ]
      ambientIntegralRowModule (K := K) m :=
  ((ambientKernelSubmodule (K := K) V).mkQ).exists_rightInverse_of_surjective
    (ambientKernelSubmodule (K := K) V).range_mkQ |>.choose

/- [derived consequence, paper `le:low_rank_induction`, lines 1477--1479]
   The chosen section is a right inverse to the quotient map. -/
theorem ambientKernelQuotientSection_spec {m l : ℕ}
    (V : Grassmannian K m l) :
    (ambientKernelSubmodule (K := K) V).mkQ.comp
      (ambientKernelQuotientSection (K := K) V) = LinearMap.id :=
  ((ambientKernelSubmodule (K := K) V).mkQ).exists_rightInverse_of_surjective
    (ambientKernelSubmodule (K := K) V).range_mkQ |>.choose_spec

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  Restrict the orthogonal projection to the ambient integral
   lattice and corestrict it to its image.  This names the quotient map whose
   target is exactly the projected lattice in the manuscript. -/
noncomputable def ambientProjectedRowMap {m l : ℕ}
    (V : Grassmannian K m l) :
    ambientIntegralRowModule (K := K) m →ₗ[ℤ]
      projectedAmbientRowModule (K := K) V :=
  LinearMap.codRestrict (projectedAmbientRowModule (K := K) V)
    ((projectedAmbientRowMap V).domRestrict
      (ambientIntegralRowModule (K := K) m))
    (fun x => Submodule.mem_map.mpr ⟨x, x.property, rfl⟩)

/- [derived consequence, paper `le:low_rank_induction`, lines 1477--1479]
   On underlying Minkowski vectors, the corestricted map is the manuscript's
   orthogonal projection. -/
theorem ambientProjectedRowMap_apply {m l : ℕ}
    (V : Grassmannian K m l) (x : ambientIntegralRowModule (K := K) m) :
    (ambientProjectedRowMap (K := K) V x : (rowRealSpan V)ᗮ) =
      projectedAmbientRowMap V x := rfl

/- [derived consequence, paper `le:low_rank_induction`, lines 1477--1479]
   The kernel of the ambient-to-projected map is the primitive lower lattice,
   now expressed on the ambient carrier. -/
theorem ker_ambientProjectedRowMap_eq_ambientKernelSubmodule
    {m l : ℕ} (V : Grassmannian K m l) :
    LinearMap.ker (ambientProjectedRowMap (K := K) V) =
      ambientKernelSubmodule (K := K) V := by
  ext x
  constructor
  · intro hx
    change ambientProjectedRowMap (K := K) V x = 0 at hx
    rw [mem_ambientKernelSubmodule_iff]
    rw [← ambientIntegralRowModule_inf_kernel_projectedAmbientRowMap_eq V]
    refine ⟨x.property, ?_⟩
    calc
      projectedAmbientRowMap V (x : RowVector K m) =
          (ambientProjectedRowMap (K := K) V x : (rowRealSpan V)ᗮ) :=
        (ambientProjectedRowMap_apply V x).symm
      _ = 0 := congrArg Subtype.val hx
  · intro hx
    change ambientProjectedRowMap (K := K) V x = 0
    apply Subtype.ext
    rw [mem_ambientKernelSubmodule_iff] at hx
    rw [← ambientIntegralRowModule_inf_kernel_projectedAmbientRowMap_eq V] at hx
    change (ambientProjectedRowMap (K := K) V x : (rowRealSpan V)ᗮ) = 0
    rw [ambientProjectedRowMap_apply]
    exact hx.2

/- [derived consequence, paper `le:low_rank_induction`, lines 1477--1479]
   By its image definition, every projected lattice vector has an integral
   ambient lift. -/
theorem ambientProjectedRowMap_surjective {m l : ℕ}
    (V : Grassmannian K m l) :
    Function.Surjective (ambientProjectedRowMap (K := K) V) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := y.property
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  change (ambientProjectedRowMap (K := K) V ⟨x, hx⟩ :
    (rowRealSpan V)ᗮ) = (y : (rowRealSpan V)ᗮ)
  rw [ambientProjectedRowMap_apply]
  exact hxy

/- [derived consequence, paper `le:low_rank_induction`, lines 1477--1479]
   First isomorphism theorem for the projected lattice: the free quotient of
   the ambient integral lattice by `Λ_{D'}` is identified with its orthogonal
   projection.  This is a proved integral equivalence, not a replacement of
   the paper's projected-lattice construction. -/
noncomputable def ambientKernelQuotientEquivProjected {m l : ℕ}
    (V : Grassmannian K m l) :
    ((ambientIntegralRowModule (K := K) m) ⧸
      ambientKernelSubmodule (K := K) V) ≃ₗ[ℤ]
      projectedAmbientRowModule (K := K) V :=
  (Submodule.quotEquivOfEq
      (LinearMap.ker (ambientProjectedRowMap (K := K) V))
      (ambientKernelSubmodule (K := K) V)
      (ker_ambientProjectedRowMap_eq_ambientKernelSubmodule V)).symm.trans
    ((ambientProjectedRowMap (K := K) V).quotKerEquivOfSurjective
      (ambientProjectedRowMap_surjective V))

theorem rowRealSpan_finrank {m k : ℕ} (V : Grassmannian K m k) :
    Module.finrank ℝ (rowRealSpan V) = k * degree K := by
  letI : Module.Finite ℚ V.1 := FiniteDimensional.trans ℚ K V.1
  letI : Fintype (RowSpaceBasisIndex V) := Fintype.ofFinite _
  rw [rowRealSpan_eq_span_embeddedRowBasisQ V,
    finrank_span_eq_card (embeddedRowBasisQ_linearIndependent V),
    ← Module.finrank_eq_card_chooseBasisIndex ℚ V.1,
    ← Module.finrank_mul_finrank ℚ K V.1, V.2]
  simp [degree, Nat.mul_comm]

theorem projectedAmbientRowModule_finrank {m l : ℕ}
    (V : Grassmannian K m l) :
    Module.finrank ℝ
        (Submodule.span ℝ
          (projectedAmbientRowModule (K := K) V : Set ((rowRealSpan V)ᗮ))) =
      m * degree K - l * degree K := by
  rw [projectedAmbientRowModule_span_top, finrank_top]
  rw [← rowRealSpan_finrank V, ← rowVector_finrank (K := K) (m := m)]
  exact Nat.eq_sub_of_add_eq
    (by simpa [Nat.add_comm] using
      (rowRealSpan V).finrank_add_finrank_orthogonal)

/- [derived consequence, paper le:low_rank_induction, lines 1475--1479]
   The rational and real spans of the projected ambient module have the same
   dimension.  The rational calculation uses the ambient Minkowski image,
   the proved real-span/kernel bridge, and rank--nullity over ℚ; the real
   calculation is the preceding projected-span dimension theorem. -/
theorem projectedAmbientRowModule_rat_finrank_eq_real_finrank
    {m l : ℕ} (V : Grassmannian K m l) :
    Set.finrank ℚ
        (projectedAmbientRowModule (K := K) V :
          Set ((rowRealSpan V)ᗮ)) =
      Set.finrank ℝ
        (projectedAmbientRowModule (K := K) V :
          Set ((rowRealSpan V)ᗮ)) := by
  let W := (rowRealSpan V)ᗮ
  letI : Module ℚ W := Module.compHom W (algebraMap ℚ ℝ)
  let embed := ambientRowEmbeddingQ (K := K) m
  let P : RowVector K m →ₗ[ℝ] W :=
    ((rowRealSpan V)ᗮ.orthogonalProjectionOnto).toLinearMap
  let Pq : (Fin m → K) →ₗ[ℚ] W :=
    (P.restrictScalars ℚ).comp embed
  have hspan_ambient :
      Submodule.span ℚ
          (ambientIntegralRowModule (K := K) m : Set (RowVector K m)) =
        LinearMap.range embed :=
    ambientIntegralRowModule_ratSpan_eq_range (K := K) m
  have hdouble : (rowRealSpan V)ᗮᗮ = rowRealSpan V := by
    rw [Submodule.orthogonal_orthogonal_eq_closure]
    exact (Submodule.closed_of_finiteDimensional _).submodule_topologicalClosure_eq
  have hker : LinearMap.ker Pq = (V.1.restrictScalars ℚ) := by
    apply le_antisymm
    · intro x hx
      change P (embed x) = 0 at hx
      have hzero : P (embed x) = 0 := hx
      have hmem : embed x ∈ (rowRealSpan V)ᗮᗮ := by
        exact (Submodule.orthogonalProjectionOnto_eq_zero_iff).mp hzero
      rw [hdouble] at hmem
      exact rowRealSpan_mem_ambient_to_mem V x hmem
    · intro x hx
      change x ∈ V.1 at hx
      have hxrat : (⟨x, hx⟩ : V.1) ∈ Submodule.span ℚ
          (Set.range (fun v : integralRowModule V =>
            (integralRowToRowSpace V v : V.1))) := by
        rw [span_range_integralRowToRowSpace_rat V]
        trivial
      have hmem : rowSpaceVectorEmbeddingQ V ⟨x, hx⟩ ∈ rowRealSpan V :=
        rowSpaceVectorEmbeddingQ_mem_rowRealSpan_of_mem_ratSpan V
          ⟨x, hx⟩ hxrat
      change P (embed x) = 0
      have hembed : embed x = rowSpaceVectorEmbeddingQ V ⟨x, hx⟩ := by
        apply PiLp.ext
        intro j
        rfl
      rw [hembed]
      exact Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero hmem
  have hspan_projected :
      Submodule.span ℚ
          (projectedAmbientRowModule (K := K) V : Set W) =
        LinearMap.range Pq := by
    let S : Submodule ℚ W :=
      Submodule.span ℚ
        (projectedAmbientRowModule (K := K) V : Set W)
    have hP : ∀ x : RowVector K m,
        x ∈ Submodule.span ℚ
          (ambientIntegralRowModule (K := K) m : Set (RowVector K m)) →
          P x ∈ S := by
      intro x hx
      refine Submodule.span_induction (p := fun y _ => P y ∈ S) ?_ ?_ ?_ ?_ hx
      · intro y hy
        apply Submodule.subset_span
        exact projectedAmbientRowMap_mem_projectedAmbientRowModule V hy
      · simpa [P] using S.zero_mem
      · intro y z _ _ hy hz
        simpa [P, map_add] using S.add_mem hy hz
      · intro q y _ hy
        have hq := P.map_smul (q : ℝ) y
        rw [Rat.cast_smul_eq_qsmul ℝ q (P y)] at hq
        change P ((q : ℝ) • y) ∈ S
        rw [hq]
        exact S.smul_mem q hy
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hy' : y ∈ Submodule.span ℚ
          (ambientIntegralRowModule (K := K) m : Set (RowVector K m)) :=
        Submodule.subset_span hy
      rw [hspan_ambient] at hy'
      obtain ⟨w, hw⟩ := hy'
      refine ⟨w, ?_⟩
      calc
        Pq w = P (embed w) := rfl
        _ = P y := congrArg P hw
        _ = projectedAmbientRowMap V y := rfl
    · intro x hx
      obtain ⟨w, rfl⟩ := hx
      apply hP
      rw [hspan_ambient]
      exact ⟨w, rfl⟩
  change Module.finrank ℚ (Submodule.span ℚ
      (projectedAmbientRowModule (K := K) V : Set W)) =
    Module.finrank ℝ (Submodule.span ℝ
      (projectedAmbientRowModule (K := K) V : Set W))
  rw [hspan_projected]
  have hdim : Module.finrank ℚ (Fin m → K) = m * degree K := by
    rw [Module.finrank_pi_fintype]
    simp [degree]
  have hdomain : FiniteDimensional ℚ (Fin m → K) := by infer_instance
  have hkerfin : Module.finrank ℚ (LinearMap.ker Pq) = l * degree K := by
    rw [hker]
    change Module.finrank ℚ V.1 = l * degree K
    rw [← Module.finrank_mul_finrank ℚ K V.1, V.2]
    simp [degree, Nat.mul_comm]
  have hqrank : Module.finrank ℚ (LinearMap.range Pq) =
      m * degree K - l * degree K := by
    have hrank := Pq.finrank_range_add_finrank_ker
    rw [hdim, hkerfin] at hrank
    exact Nat.eq_sub_of_add_eq hrank
  have hrealrank : Module.finrank ℝ
      (Submodule.span ℝ
        (projectedAmbientRowModule (K := K) V : Set W)) =
      m * degree K - l * degree K := projectedAmbientRowModule_finrank V
  exact hqrank.trans hrealrank.symm

/- [derived consequence, paper low_rank_induction, lines 1475--1479]
   The projected ambient module is discrete.  This application is now
   unconditional: finite generation was proved above, and the rational/real
   span equality is the preceding rank calculation. -/
noncomputable instance projectedAmbientRowModule.discreteTopology
    {m l : ℕ} (V : Grassmannian K m l) :
    DiscreteTopology (projectedAmbientRowModule (K := K) V) := by
  apply discreteTopology_of_finrank_eq
  exact projectedAmbientRowModule_rat_finrank_eq_real_finrank V

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   The projected module is full in its ambient real vector space, hence has
   the `IsZLattice` interface required by the lattice-counting lemmas.  Its
   exact covolume normalization is deliberately not inferred here. -/
noncomputable instance projectedAmbientRowModule.isZLattice
    {m l : ℕ} (V : Grassmannian K m l) :
    IsZLattice ℝ (projectedAmbientRowModule (K := K) V) :=
  ⟨projectedAmbientRowModule_span_top V⟩

/- The real span is stable under the paper's `K_ℝ`-action.  On an integral
   generator, expand the `K_ℝ` scalar in the Minkowski images of the integral
   basis and use the `𝓞_K`-module structure of `Λ_D`; the remaining cases are
   the linearity axioms of a real span. -/
theorem kReal_smul_mem_rowRealSpan {m k : ℕ}
    (V : Grassmannian K m k) (c : K_ℝ[K]) {x : RowVector K m}
    (hx : x ∈ rowRealSpan V) : c • x ∈ rowRealSpan V := by
  rw [rowRealSpan] at hx ⊢
  refine Submodule.span_induction
    (p := fun y : RowVector K m => fun _ => c • y ∈ rowRealSpan V)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨v, hv, rfl⟩ :=
      (mem_embeddedIntegralRowModule_iff V y).1 hy
    let v' : integralRowModule V := ⟨v, hv⟩
    change c • integralVectorEmbedding (K := K) m v' ∈ rowRealSpan V
    obtain ⟨a, ha⟩ := exists_real_combination_numberEmbedding (K := K) c
    rw [ha, Finset.sum_smul]
    apply (rowRealSpan V).sum_mem
    intro i hi
    let vi : integralRowModule V :=
      (NumberField.RingOfIntegers.basis K i) • v'
    have hmul : numberEmbedding K
          (NumberField.integralBasis K i : K) •
          integralVectorEmbedding (K := K) m v' =
        integralVectorEmbedding (K := K) m vi := by
      apply PiLp.ext
      intro j
      change numberEmbedding K (NumberField.integralBasis K i : K) •
          numberEmbedding K (v'.1 j : K) =
        numberEmbedding K (((NumberField.RingOfIntegers.basis K i) • v').1 j : K)
      rw [smul_eq_mul]
      simpa [NumberField.integralBasis_apply] using
        (map_mul (numberEmbeddingRingHom K)
          (NumberField.integralBasis K i : K) (v'.1 j : K)).symm
    rw [smul_assoc]
    rw [hmul]
    exact (rowRealSpan V).smul_mem (a i)
      (Submodule.subset_span ((mem_embeddedIntegralRowModule_iff V _).2
        ⟨vi.1, vi.2, rfl⟩))
  · simpa using (rowRealSpan V).zero_mem
  · intro y z _ _ hy hz
    simpa [smul_add] using (rowRealSpan V).add_mem hy hz
  · intro r y _ hy
    rw [smul_comm c r y]
    exact (rowRealSpan V).smul_mem r hy

/- The subtype `rowRealSpan V` now carries the same genuine `K_ℝ`-module
   structure as its ambient real span. -/
noncomputable instance rowRealSpanSMul {m k : ℕ}
    (V : Grassmannian K m k) : SMul K_ℝ[K] (rowRealSpan V) where
  smul := fun c x =>
    ⟨c • (x : RowVector K m), kReal_smul_mem_rowRealSpan V c x.property⟩

noncomputable instance rowRealSpanModule {m k : ℕ}
    (V : Grassmannian K m k) : Module K_ℝ[K] (rowRealSpan V) where
  one_smul x := by
    apply Subtype.ext
    change (1 : K_ℝ[K]) • (x : RowVector K m) = (x : RowVector K m)
    simp
  mul_smul c d x := by
    apply Subtype.ext
    change (c * d) • (x : RowVector K m) =
      c • d • (x : RowVector K m)
    simp [mul_smul]
  smul_zero c := by
    apply Subtype.ext
    change c • (0 : RowVector K m) = 0
    simp
  smul_add c x y := by
    apply Subtype.ext
    change c • ((x : RowVector K m) + (y : RowVector K m)) =
      c • (x : RowVector K m) + c • (y : RowVector K m)
    simp [smul_add]
  add_smul c d x := by
    apply Subtype.ext
    change (c + d) • (x : RowVector K m) =
      c • (x : RowVector K m) + d • (x : RowVector K m)
    simp [add_smul]
  zero_smul x := by
    apply Subtype.ext
    change (0 : K_ℝ[K]) • (x : RowVector K m) = 0
    simp

noncomputable instance rowRealSpanKRealIsScalarTower {m k : ℕ}
    (V : Grassmannian K m k) :
    IsScalarTower ℝ K_ℝ[K] (rowRealSpan V) where
  smul_assoc r c x := by
    apply Subtype.ext
    change (r • c) • (x : RowVector K m) = r • (c • (x : RowVector K m))
    exact smul_assoc r c (x : RowVector K m)

/- The manuscript's successive minima use the number-field `K`-action.  This
   is the restriction of the preceding `K_ℝ`-module structure along the
   proved embedding `K →+* K_ℝ`; the larger `K_ℝ`-action is reserved for the
   real lines used in the projection estimate. -/
noncomputable instance rowRealSpanKModule {m k : ℕ}
    (V : Grassmannian K m k) : Module K (rowRealSpan V) :=
  Module.compHom (rowRealSpan V) (numberEmbeddingRingHom K)

/- The two actions are compatible through the algebra embedding `K → K_ℝ`.
   This lets `K`-spans be compared with the larger `K_ℝ`-spans used in the
   covering-radius argument. -/
noncomputable instance rowRealSpanK_KRealIsScalarTower {m k : ℕ}
    (V : Grassmannian K m k) :
    IsScalarTower K K_ℝ[K] (rowRealSpan V) := by
  constructor
  intro c a x
  apply Subtype.ext
  change (numberEmbedding K c * a) • (x : RowVector K m) =
    numberEmbedding K c • (a • (x : RowVector K m))
  exact mul_smul _ _ _

/- The same lattice, now regarded as a full lattice in its real span. -/
noncomputable def rowZLattice {m k : ℕ} (V : Grassmannian K m k) :
    Submodule ℤ (rowRealSpan V) :=
  Submodule.comap ((rowRealSpan V).subtype.restrictScalars ℤ)
    (embeddedIntegralRowModule V)

/- [Derived consequence] The subtype inclusion of the real row span into the
   ambient Minkowski row space is also `K`-linear for the genuine restricted
   `K`-action.  This map is used only to transfer the finite-dimensional
   rational `K`-span calculation to the real-span subtype. -/
noncomputable def rowRealSpanSubtypeKLinearMap {m k : ℕ}
    (V : Grassmannian K m k) :
    rowRealSpan V →ₗ[K] RowVector K m where
  toFun x := x.1
  map_add' x y := rfl
  map_smul' c x := by
    rfl

theorem rowRealSpanSubtypeKLinearMap_injective {m k : ℕ}
    (V : Grassmannian K m k) :
    Function.Injective (rowRealSpanSubtypeKLinearMap V) := by
  intro x y hxy
  exact Subtype.ext hxy

theorem rowRealSpanSubtypeKLinearMap_image_rowZLattice {m k : ℕ}
    (V : Grassmannian K m k) :
    rowRealSpanSubtypeKLinearMap V '' (rowZLattice V : Set (rowRealSpan V)) =
      (embeddedIntegralRowModule V : Set (RowVector K m)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (y : RowVector K m) ∈ embeddedIntegralRowModule V at hy
    exact hy
  · intro hx
    have hy : x ∈ rowRealSpan V := Submodule.subset_span hx
    refine ⟨⟨x, hy⟩, ?_, rfl⟩
    change x ∈ embeddedIntegralRowModule V
    exact hx

/- The `K`-span of the one-row lattice has the expected rank `k`.  This is
   the algebraic rank bridge needed by the recursive minima proof; the
   real-span dimension remains `k * degree K` as in the manuscript. -/
theorem rowZLattice_K_span_finrank {m k : ℕ}
    (V : Grassmannian K m k) :
    Module.finrank K
        (Submodule.span K (rowZLattice V : Set (rowRealSpan V))) = k := by
  let S : Submodule K (rowRealSpan V) :=
    Submodule.span K (rowZLattice V : Set (rowRealSpan V))
  let fS : S →ₗ[K] RowVector K m :=
    (rowRealSpanSubtypeKLinearMap V).domRestrict S
  have hmap : S.map (rowRealSpanSubtypeKLinearMap V) =
      Submodule.span K (embeddedIntegralRowModule V : Set (RowVector K m)) := by
    rw [Submodule.map_span]
    rw [rowRealSpanSubtypeKLinearMap_image_rowZLattice V]
  have hfS : Function.Injective fS := by
    intro x y hxy
    apply Subtype.ext
    apply rowRealSpanSubtypeKLinearMap_injective V
    exact hxy
  have hrange : LinearMap.range fS =
      Submodule.span K (embeddedIntegralRowModule V : Set (RowVector K m)) := by
    rw [LinearMap.range_domRestrict]
    exact hmap
  change Module.finrank K S = k
  calc
    Module.finrank K S = Module.finrank K (LinearMap.range fS) :=
      (LinearMap.finrank_range_of_inj hfS).symm
    _ = Module.finrank K
        (Submodule.span K (embeddedIntegralRowModule V : Set (RowVector K m))) :=
      congrArg (fun W : Submodule K (RowVector K m) => Module.finrank K W) hrange
    _ = k := span_embeddedIntegralRowModule_finrank V

/- The same transfer also supplies the finite-dimensional instance required by
   the standard submodule equality lemmas. -/
theorem rowZLattice_K_span_finiteDimensional {m k : ℕ}
    (V : Grassmannian K m k) :
    FiniteDimensional K
        (Submodule.span K (rowZLattice V : Set (rowRealSpan V))) := by
  let S : Submodule K (rowRealSpan V) :=
    Submodule.span K (rowZLattice V : Set (rowRealSpan V))
  let W : Submodule K (RowVector K m) :=
    Submodule.span K (embeddedIntegralRowModule V : Set (RowVector K m))
  have hmap : S.map (rowRealSpanSubtypeKLinearMap V) = W := by
    rw [Submodule.map_span]
    rw [rowRealSpanSubtypeKLinearMap_image_rowZLattice V]
  letI : FiniteDimensional K W := by
    change FiniteDimensional K
      (Submodule.span K (embeddedIntegralRowModule V : Set (RowVector K m)))
    rw [span_embeddedIntegralRowModule_eq_range_rowSpaceVectorEmbeddingK V]
    infer_instance
  let fS : S →ₗ[K] W :=
    ((rowRealSpanSubtypeKLinearMap V).domRestrict S).codRestrict W (fun x => by
      rw [← hmap]
      exact ⟨x, x.property, rfl⟩)
  have hfS : Function.Injective fS := by
    intro x y hxy
    apply Subtype.ext
    apply rowRealSpanSubtypeKLinearMap_injective V
    exact congrArg (fun z : W => (z : RowVector K m)) hxy
  exact FiniteDimensional.of_injective fS hfS

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
      (Subtype.val ⁻¹' (embeddedIntegralRowModule V : Set (RowVector K m))) = ⊤
  exact eq_top_iff.mpr Submodule.span_span_coe_preimage.symm.le

/- [Lean infrastructure] Make the freeness used by the chosen integral basis
   explicit.  This is the general discrete-submodule instance, independent of
   the height computation. -/
noncomputable instance rowZLattice.moduleFree {m k : ℕ}
    (V : Grassmannian K m k) : Module.Free ℤ (rowZLattice V) := by
  exact instModuleFree_of_discrete_submodule (rowZLattice V)

/- [Lean infrastructure] This is the covolume of the primitive row lattice in
   Mathlib's unscaled Euclidean mixed-space metric.  The manuscript's height
   uses the discriminant/trace metric in `eq:norm` (papers/katznelson.tex,
   lines 661--674).  The two fixed-field metrics are uniformly equivalent on
   every fixed-dimensional row space, which is enough for the coarse
   counting and successive-minima estimates.  This raw covolume is not by
   itself used to identify the manuscript's exact main-term constant; the
   exact normalized coefficient measure and denominator bridge are proved in
   `Counting/MainTermNormalization.lean`.
   Schmidt's 1967 paper supplies the height-counting argument, and Thunder's
   1992 paper gives a sharper asymptotic in its own normalization. -/
noncomputable def rowSpaceHeight {m k : ℕ}
    (V : Grassmannian K m k) : ℝ :=
  ZLattice.covolume (rowZLattice V)
    (μHE[Module.finrank ℝ (rowRealSpan V)])

theorem rowSpaceHeight_pos {m k : ℕ} (V : Grassmannian K m k) :
    0 < rowSpaceHeight V := by
  exact ZLattice.covolume_pos (rowZLattice V)
    (μHE[Module.finrank ℝ (rowRealSpan V)])

/- [Lean infrastructure] This is the exact bridge between the two Mathlib
   measures used internally.  It does not identify either one with the
   discriminant/trace-normalized Euclidean measure in the manuscript. -/
theorem rowSpaceHeight_eq_volume_covolume {m k : ℕ}
    (V : Grassmannian K m k) :
    rowSpaceHeight V =
      ZLattice.covolume (rowZLattice V)
        (volume : Measure (rowRealSpan V)) := by
  rw [rowSpaceHeight]
  congr 1
  exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume

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
      ∀ i, rowVectorOfFun (A i) ∈ embeddedIntegralRowModule V := by
  constructor
  · rintro ⟨B, hB, rfl⟩ i
    exact (mem_embeddedIntegralRowModule_iff V
      (rowVectorOfFun (embedMatrix B i))).2
      ⟨B.row i, hB i, rfl⟩
  · intro hA
    choose v hv using fun i =>
      (mem_embeddedIntegralRowModule_iff V (rowVectorOfFun (A i))).1 (hA i)
    let B : IntegralMatrix K n m := fun i => v i
    have hB : rowsInIntegralRowModule V B := by
      intro i
      exact (hv i).1
    have hBA : embedMatrix B = A := by
      ext i j
      have hrow := congrArg WithLp.ofLp (hv i).2
      exact congrFun hrow j
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

/- [Lean infrastructure] The matrix wrapper has a canonical Borel structure
   from `Foundations`, but elaborating `μHE` through the submodule wrapper can
   select the measurable-space argument before the Borel instance.  This is
   the same Euclidean Hausdorff measure with those arguments made explicit. -/
noncomputable def rowMatrixEuclideanMeasure {m k n : ℕ}
    (V : Grassmannian K m k) :
    @Measure (rowMatrixRealSpan V n)
      (@Subtype.instMeasurableSpace (M n m (K_ℝ[K]))
        (fun A => A ∈ rowMatrixRealSpan V n)
        (kRealMatrixMeasurableSpace (K := K))) :=
  @MeasureTheory.Measure.euclideanHausdorffMeasure
    (rowMatrixRealSpan V n) inferInstance
    (@Subtype.instMeasurableSpace (M n m (K_ℝ[K]))
      (fun A => A ∈ rowMatrixRealSpan V n)
      (kRealMatrixMeasurableSpace (K := K)))
    (@Subtype.borelSpace (M n m (K_ℝ[K])) inferInstance
      (kRealMatrixMeasurableSpace (K := K))
      (kRealMatrixBorelSpace (K := K))
      (fun A => A ∈ rowMatrixRealSpan V n))
    (Module.finrank ℝ (rowMatrixRealSpan V n))

/- The rowwise submodule of matrices whose rows lie in the real row span. -/
def rowMatrixRowwiseSubmodule {m k n : ℕ}
    (V : Grassmannian K m k) :
    Submodule ℝ (M n m (K_ℝ[K])) where
  carrier := {A | ∀ i, rowVectorOfFun (A i) ∈ rowRealSpan V}
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
    A ∈ rowMatrixRowwiseSubmodule V ↔
      ∀ i, rowVectorOfFun (A i) ∈ rowRealSpan V := Iff.rfl

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
    exact (mem_embeddedIntegralRowModule_iff V
      (rowVectorOfFun (embedMatrix B i))).2 ⟨B.row i, hB i, rfl⟩
  · intro A hA
    have hsingle (i : Fin n) {x : RowVector K m}
        (hx : x ∈ rowRealSpan V) :
        (Pi.single i x.ofLp : M n m (K_ℝ[K])) ∈ rowMatrixRealSpan V n := by
      rw [rowRealSpan] at hx
      refine Submodule.span_induction (p := fun y _ =>
        (Pi.single i y.ofLp : M n m (K_ℝ[K])) ∈ rowMatrixRealSpan V n)
        ?_ ?_ ?_ ?_ hx
      · intro y hy
        obtain ⟨v, hv, hvy⟩ :=
          (mem_embeddedIntegralRowModule_iff V _).1 hy
        have hvy' : y.ofLp = (integralVectorEmbedding (K := K) m v).ofLp :=
          congrArg WithLp.ofLp hvy.symm
        rw [hvy']
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
            (Pi.single i (integralVectorEmbedding (K := K) m v).ofLp :
              M n m (K_ℝ[K])) =
              embedMatrix (Pi.single i v : IntegralMatrix K n m) := by
          ext j l
          by_cases hji : j = i
          · subst j
            simp [embedMatrix]
          · simp [embedMatrix, Pi.single_apply, hji]
        rw [hmatrix]
        exact hspan
      · have hzero : (Pi.single i ((0 : RowVector K m).ofLp) :
            M n m (K_ℝ[K])) =
            (0 : M n m (K_ℝ[K])) := by
          ext j l
          simp
        rw [hzero]
        exact (rowMatrixRealSpan V n).zero_mem
      · intro y z _ _ hy hz
        have hadd : (Pi.single i (y + z).ofLp : M n m (K_ℝ[K])) =
            (Pi.single i y.ofLp : M n m (K_ℝ[K])) +
              Pi.single i z.ofLp := by
          ext j l
          by_cases hji : j = i
          · subst j
            simp
          · simp [Pi.single_apply, hji]
        have h := (rowMatrixRealSpan V n).add_mem hy hz
        rw [hadd]
        exact h
      · intro c y _ hy
        have hsmul : (Pi.single i (c • y).ofLp : M n m (K_ℝ[K])) =
            c • (Pi.single i y.ofLp : M n m (K_ℝ[K])) := by
          ext j l
          by_cases hji : j = i
          · subst j
            simp
          · simp [Pi.single_apply, hji]
        have h := (rowMatrixRealSpan V n).smul_mem c hy
        rw [hsmul]
        exact h
    change ∀ i, rowVectorOfFun (A i) ∈ rowRealSpan V at hA
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
      ⟨rowVectorOfFun (A.1 i), by
        have hA : (A : M n m (K_ℝ[K])) ∈
            rowMatrixRowwiseSubmodule V := by
          rw [← rowMatrixRealSpan_eq_rowwise V]
          exact A.2
        exact hA i⟩
    invFun := fun A =>
      ⟨fun i => (A i).1.ofLp, by
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

/- [derived consequence, paper `le:without_rank_cond`, lines 1038--1044]
   The preceding algebraic row decomposition becomes an isometry after the
   outer finite product is also given its `l²` norm. -/
noncomputable def rowMatrixRealSpanLpEquiv {m k n : ℕ}
    (V : Grassmannian K m k) :
    rowMatrixRealSpan V n ≃ₗ[ℝ]
      PiLp 2 (fun _ : Fin n => rowRealSpan V) :=
  (rowMatrixRealSpanEquiv V).trans
    (WithLp.linearEquiv 2 ℝ (Fin n → rowRealSpan V)).symm

theorem rowMatrixRealSpanLpEquiv_norm {m k n : ℕ}
    (V : Grassmannian K m k) (A : rowMatrixRealSpan V n) :
    ‖rowMatrixRealSpanLpEquiv V A‖ = ‖A‖ := by
  change ‖WithLp.toLp 2 (fun i =>
    (rowMatrixRealSpanEquiv V A) i)‖ =
      ‖(A : M n m (K_ℝ[K]))‖
  rw [PiLp.norm_eq_of_L2, Matrix.frobenius_norm_def]
  rw [Real.sqrt_eq_rpow]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change ‖rowVectorOfFun ((A : M n m (K_ℝ[K])) i)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp [rowMatrixRealSpanEquiv, rowVectorOfFun]

noncomputable def rowMatrixRealSpanLpIsometryEquiv {m k n : ℕ}
    (V : Grassmannian K m k) :
    rowMatrixRealSpan V n ≃ₗᵢ[ℝ]
      PiLp 2 (fun _ : Fin n => rowRealSpan V) :=
  { toLinearEquiv := rowMatrixRealSpanLpEquiv V
    norm_map' := fun A => rowMatrixRealSpanLpEquiv_norm V A }

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
    {m k n : ℕ} (V : Grassmannian K m k) :
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

theorem rowMatrixZLattice_discreteTopology {m k n : ℕ}
    (V : Grassmannian K m k) : DiscreteTopology (rowMatrixZLattice V n) :=
  rowMatrixZLattice.discreteTopology V

noncomputable instance rowMatrixZLattice.isZLattice {m k n : ℕ}
    (V : Grassmannian K m k) :
    @IsZLattice ℝ inferInstance (rowMatrixRealSpan V n)
      inferInstance inferInstance (rowMatrixZLattice V n)
      (rowMatrixZLattice_discreteTopology V) :=
  @IsZLattice.mk ℝ inferInstance (rowMatrixRealSpan V n)
    inferInstance inferInstance (rowMatrixZLattice V n)
    (rowMatrixZLattice_discreteTopology V) (rowMatrixZLattice_span_top V n)

/- [Lean infrastructure] The product lattice in the `l²` product of the
   one-row spans.  This is the internal product realization of the paper's
   `M_n(Λ_D)`; the proved isometry/comap bridge below connects it to the
   matrix realization. -/
def rowProductZLattice {m k n : ℕ} (V : Grassmannian K m k) :
    Submodule ℤ (PiLp 2 (fun _ : Fin n => rowRealSpan V)) where
  carrier := {A | ∀ i, A i ∈ rowZLattice V}
  zero_mem' := by
    intro i
    exact (rowZLattice V).zero_mem
  add_mem' := by
    intro A B hA hB i
    exact (rowZLattice V).add_mem (hA i) (hB i)
  smul_mem' := by
    intro a A hA i
    exact (rowZLattice V).smul_mem a (hA i)

@[simp]
theorem mem_rowProductZLattice_iff {m k n : ℕ}
    (V : Grassmannian K m k)
    (A : PiLp 2 (fun _ : Fin n => rowRealSpan V)) :
    A ∈ rowProductZLattice V ↔ ∀ i, A i ∈ rowZLattice V := Iff.rfl

/- [derived consequence, paper `le:without_rank_cond`, lines 1038--1044]
   Coordinatewise covering bounds combine with the Euclidean product norm by
   the factor `√n`.  This is the formal product-radius estimate; its intended
   use is with the intrinsic covering bounds supplied by the Voronoi/radius
   development, not with `latticeFundamentalRadius`. -/
theorem rowProductZLattice_isLatticeCovering_of_isLatticeCovering
    {m k n : ℕ} (V : Grassmannian K m k) {R : ℝ} (hR : 0 ≤ R)
    (hcover : LatticeCovering (rowZLattice V) R) :
    LatticeCovering (rowProductZLattice (n := n) V) (Real.sqrt (n : ℝ) * R) := by
  intro x
  let v : Fin n → rowZLattice V := fun i =>
    Classical.choose (hcover (x i))
  have hv : ∀ i : Fin n,
      dist (x i) ((v i : rowZLattice V) : rowRealSpan V) ≤ R := by
    intro i
    exact Classical.choose_spec (hcover (x i))
  let y : rowProductZLattice (n := n) V :=
    ⟨WithLp.toLp 2 (fun i => ((v i : rowZLattice V) : rowRealSpan V)), by
      intro i
      exact (v i).2⟩
  refine ⟨y, ?_⟩
  calc
    dist x (y : PiLp 2 (fun _ : Fin n => rowRealSpan V)) =
        Real.sqrt (∑ i : Fin n,
          dist (x i) ((y : PiLp 2 (fun _ : Fin n => rowRealSpan V)) i) ^ 2) :=
      PiLp.dist_eq_of_L2 x y
    _ ≤ Real.sqrt (∑ i : Fin n, R ^ 2) := by
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro i hi
      exact (sq_le_sq₀ (dist_nonneg) hR).mpr (hv i)
    _ = Real.sqrt (n : ℝ) * R := by
      rw [Finset.sum_const, Finset.card_fin]
      have hn : 0 ≤ (n : ℝ) := by positivity
      have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
      have hsq : (Real.sqrt (n : ℝ) * R) ^ 2 = (n : ℝ) * R ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hn]
      rw [nsmul_eq_mul, ← hsq, Real.sqrt_sq (mul_nonneg hsqrt hR)]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem rowProductZLattice_eq_comap {m k n : ℕ}
    (V : Grassmannian K m k) :
    rowProductZLattice V =
      ZLattice.comap ℝ (rowMatrixZLattice V n)
        (rowMatrixRealSpanLpIsometryEquiv (n := n) V).symm.toLinearMap := by
  ext A
  constructor
  · intro hA
    change ∀ i, (A i : RowVector K m) ∈ embeddedIntegralRowModule V at hA
    change (rowMatrixRealSpanLpIsometryEquiv (n := n) V).symm A ∈
      rowMatrixZLattice V n
    change ((rowMatrixRealSpanLpIsometryEquiv (n := n) V).symm A :
      rowMatrixRealSpan V n) ∈ rowMatrixZLattice V n
    change ((rowMatrixRealSpanLpIsometryEquiv (n := n) V).symm A :
      M n m (K_ℝ[K])) ∈ embeddedRowMatrixModule V n
    rw [mem_embeddedRowMatrixModule_iff_rows]
    intro i
    have hrow : rowVectorOfFun
        ((((rowMatrixRealSpanLpIsometryEquiv (n := n) V).symm A :
          rowMatrixRealSpan V n) : M n m (K_ℝ[K])) i) =
        (A i : RowVector K m) := by
      have h := congrArg (fun B : PiLp 2 (fun _ : Fin n => rowRealSpan V) => B i)
          ((rowMatrixRealSpanLpIsometryEquiv (n := n) V).apply_symm_apply A)
      exact congrArg Subtype.val h
    rw [hrow]
    exact hA i
  · intro hA
    change (rowMatrixRealSpanLpIsometryEquiv (n := n) V).symm A ∈
      rowMatrixZLattice V n at hA
    rw [mem_rowProductZLattice_iff]
    intro i
    have hrow : rowVectorOfFun
        ((((rowMatrixRealSpanLpIsometryEquiv (n := n) V).symm A :
          rowMatrixRealSpan V n) : M n m (K_ℝ[K])) i) =
        (A i : RowVector K m) := by
      have h := congrArg (fun B : PiLp 2 (fun _ : Fin n => rowRealSpan V) => B i)
        ((rowMatrixRealSpanLpIsometryEquiv (n := n) V).apply_symm_apply A)
      exact congrArg Subtype.val h
    change (A i : RowVector K m) ∈ embeddedIntegralRowModule V
    rw [← hrow]
    have hrows := (mem_embeddedRowMatrixModule_iff_rows V
      (((rowMatrixRealSpanLpIsometryEquiv (n := n) V).symm A :
        rowMatrixRealSpan V n) : M n m (K_ℝ[K]))).1 hA
    exact hrows i

/- [derived consequence, paper `le:without_rank_cond`, lines 1038--1044]
   Transport the preceding product estimate through the proved Euclidean
   isometry from the row-product realization to the matrix realization. -/
theorem rowMatrixZLattice_isLatticeCovering_of_isLatticeCovering
    {m k n : ℕ} (V : Grassmannian K m k) {R : ℝ} (hR : 0 ≤ R)
    (hcover : LatticeCovering (rowZLattice V) R) :
    LatticeCovering (rowMatrixZLattice V n) (Real.sqrt (n : ℝ) * R) := by
  intro x
  let e := rowMatrixRealSpanLpIsometryEquiv (n := n) V
  obtain ⟨y, hy⟩ := rowProductZLattice_isLatticeCovering_of_isLatticeCovering
    V hR hcover (e x)
  let Y : PiLp 2 (fun _ : Fin n => rowRealSpan V) := y.1
  have hY : Y ∈ rowProductZLattice (n := n) V := by
    exact y.2
  rw [rowProductZLattice_eq_comap (n := n) V] at hY
  have hylattice : e.symm Y ∈ rowMatrixZLattice V n := by
    change e.symm Y ∈ rowMatrixZLattice V n at hY
    exact hY
  let z : rowMatrixZLattice V n := ⟨e.symm Y, hylattice⟩
  refine ⟨z, ?_⟩
  have hy' : dist (e x) Y ≤ Real.sqrt (n : ℝ) * R := by
    simpa [Y] using hy
  have hdist : dist x (e.symm Y) = dist (e x) Y := by
    rw [← e.isometry.dist_eq x (e.symm Y)]
    simp
  rw [show (z : rowMatrixRealSpan V n) = e.symm Y by rfl, hdist]
  exact hy'

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 800000 in
noncomputable instance rowProductZLattice.discreteTopology {m k n : ℕ}
    (V : Grassmannian K m k) :
    DiscreteTopology (rowProductZLattice (n := n) V) := by
  let e := rowMatrixRealSpanLpIsometryEquiv (n := n) V
  let toAmbient : rowProductZLattice (n := n) V → rowMatrixZLattice V n :=
    fun A => ⟨e.symm A.1, by
      have hA : A.1 ∈ rowProductZLattice (n := n) V := A.2
      have hA' : A.1 ∈ ZLattice.comap ℝ (rowMatrixZLattice V n)
          e.symm.toLinearMap := by
        rw [← rowProductZLattice_eq_comap (n := n) V]
        exact hA
      exact hA'⟩
  apply DiscreteTopology.of_continuous_injective (f := toAmbient)
  · apply Continuous.subtype_mk
    exact e.symm.continuous.comp continuous_subtype_val
  · intro A B hAB
    apply Subtype.ext
    apply e.symm.injective
    exact congrArg (fun z : rowMatrixZLattice V n =>
      (z : rowMatrixRealSpan V n)) hAB

noncomputable instance rowProductZLattice.isZLattice {m k n : ℕ}
    (V : Grassmannian K m k) :
    @IsZLattice ℝ _ (PiLp 2 (fun _ : Fin n => rowRealSpan V)) _ _
      (rowProductZLattice (n := n) V)
      (rowProductZLattice.discreteTopology V) := by
  refine ⟨?_⟩
  rw [rowProductZLattice_eq_comap (n := n) V]
  apply ZLattice.comap_span_top ℝ
    (L := rowMatrixZLattice V n) (rowMatrixZLattice_span_top V n)
  intro x hx
  exact ⟨(rowMatrixRealSpanLpIsometryEquiv (n := n) V) x, by simp⟩

/- [Lean infrastructure] The product lattice has the evident product basis.
   We keep the same index as the one-row lattice basis so that the determinant
   factors by coordinates. -/
noncomputable def rowProductZLatticeEquiv {m k n : ℕ}
    (V : Grassmannian K m k) :
    rowProductZLattice (n := n) V ≃ₗ[ℤ] (Fin n → rowZLattice V) := by
  let e : rowProductZLattice (n := n) V ≃ₗ[ℤ] (Fin n → rowZLattice V) := {
    toFun := fun A i => ⟨A.1 i, A.2 i⟩
    invFun := fun A =>
      ⟨WithLp.toLp 2 (fun i => (A i : rowRealSpan V)), by
        intro i
        exact (A i).2⟩
    map_add' := by
      intro A B
      ext i
      rfl
    map_smul' := by
      intro c A
      ext i
      rfl
    left_inv := by
      intro A
      apply Subtype.ext
      apply PiLp.ext
      intro i
      rfl
    right_inv := by
      intro A
      ext i
      rfl }
  exact e

abbrev rowLatticeBasisIndex {m k : ℕ} (V : Grassmannian K m k) :=
  Module.Free.ChooseBasisIndex ℤ (rowZLattice V)

noncomputable instance rowLatticeBasisIndex_fintype {m k : ℕ}
    (V : Grassmannian K m k) : Fintype (rowLatticeBasisIndex V) :=
  Fintype.ofFinite _

noncomputable def rowLatticeBasis {m k : ℕ} (V : Grassmannian K m k) :
    Basis (rowLatticeBasisIndex V) ℤ (rowZLattice V) :=
  Module.Free.chooseBasis ℤ (rowZLattice V)

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  The lower lattice occurs in two carriers: intrinsically in
   its real row span, and as the kernel submodule inside the ambient integral
   lattice.  This explicit integral equivalence keeps those carriers
   synchronized for the forthcoming block-determinant calculation. -/
noncomputable def ambientKernelEquivRowZLattice {m l : ℕ}
    (V : Grassmannian K m l) :
    ambientKernelSubmodule (K := K) V ≃ₗ[ℤ] rowZLattice V where
  toFun x :=
    ⟨⟨(x.1.1 : RowVector K m),
        Submodule.subset_span
          ((mem_ambientKernelSubmodule_iff V x.1).mp x.2)⟩,
      (mem_ambientKernelSubmodule_iff V x.1).mp x.2⟩
  invFun y := by
    have hyembed : (y.1 : RowVector K m) ∈ embeddedIntegralRowModule V := by
      exact y.2
    have hyambient : (y.1 : RowVector K m) ∈
        ambientIntegralRowModule (K := K) m := by
      have hyembed' := hyembed
      rw [embeddedIntegralRowModule_eq_ambient_inf_rowRealSpan V] at hyembed'
      exact hyembed'.1
    exact
      ⟨⟨(y.1.1 : RowVector K m), hyambient⟩,
        (mem_ambientKernelSubmodule_iff V _).mpr hyembed⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' a x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   Forgetting either carrier in the preceding equivalence gives the same
   ambient Minkowski vector. -/
theorem ambientKernelEquivRowZLattice_coe {m l : ℕ}
    (V : Grassmannian K m l) (x : ambientKernelSubmodule (K := K) V) :
    ((ambientKernelEquivRowZLattice V x : rowZLattice V) : RowVector K m) =
      (x.1 : RowVector K m) := by
  rfl

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  Transport the already chosen primitive-row basis to the
   kernel carrier inside the ambient lattice. -/
noncomputable def ambientKernelZBasis {m l : ℕ}
    (V : Grassmannian K m l) :
    Basis (rowLatticeBasisIndex V) ℤ (ambientKernelSubmodule (K := K) V) :=
  (rowLatticeBasis V).map (ambientKernelEquivRowZLattice V).symm

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   The transported kernel basis has exactly the primitive row vectors as its
   ambient values. -/
theorem ambientKernelZBasis_coe {m l : ℕ}
    (V : Grassmannian K m l) (i : rowLatticeBasisIndex V) :
    ((ambientKernelZBasis V i : ambientKernelSubmodule (K := K) V).1 :
      RowVector K m) =
      ((rowLatticeBasis V i : rowZLattice V) : RowVector K m) := by
  have h := ambientKernelEquivRowZLattice_coe V
    ((ambientKernelEquivRowZLattice V).symm (rowLatticeBasis V i))
  simpa [ambientKernelZBasis] using h.symm

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   The quotient-to-projection equivalence carries the class of an ambient
   integral vector to its orthogonal projection. -/
theorem ambientKernelQuotientEquivProjected_apply_mk {m l : ℕ}
    (V : Grassmannian K m l) (x : ambientIntegralRowModule (K := K) m) :
    ambientKernelQuotientEquivProjected V
      ((ambientKernelSubmodule (K := K) V).mkQ x) =
        ambientProjectedRowMap V x := by
  let f := ambientProjectedRowMap (K := K) V
  have hf : Function.Surjective f := ambientProjectedRowMap_surjective V
  let hk : LinearMap.ker f = ambientKernelSubmodule (K := K) V :=
    ker_ambientProjectedRowMap_eq_ambientKernelSubmodule V
  let e := Submodule.quotEquivOfEq (LinearMap.ker f)
    (ambientKernelSubmodule (K := K) V) hk
  change (f.quotKerEquivOfSurjective hf)
    (e.symm ((ambientKernelSubmodule (K := K) V).mkQ x)) = f x
  have hmk : e.symm ((ambientKernelSubmodule (K := K) V).mkQ x) =
      (LinearMap.ker f).mkQ x := by
    apply e.injective
    simp [e]
  rw [hmk]
  exact f.quotKerEquivOfSurjective_apply_mk hf x

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  Choose a basis of the projected lattice and pull it back to
   the free quotient of the ambient integral lattice.  The basis is used with
   the kernel basis above to form an integral block basis of the ambient
   lattice. -/
abbrev projectedLatticeBasisIndex {m l : ℕ} (V : Grassmannian K m l) :=
  Module.Free.ChooseBasisIndex ℤ (projectedAmbientRowModule (K := K) V)

noncomputable instance projectedLatticeBasisIndex_fintype {m l : ℕ}
    (V : Grassmannian K m l) : Fintype (projectedLatticeBasisIndex V) :=
  Fintype.ofFinite _

noncomputable def projectedLatticeBasis {m l : ℕ}
    (V : Grassmannian K m l) :
    Basis (projectedLatticeBasisIndex V) ℤ
      (projectedAmbientRowModule (K := K) V) :=
  Module.Free.chooseBasis ℤ (projectedAmbientRowModule (K := K) V)

noncomputable def ambientKernelQuotientBasis {m l : ℕ}
    (V : Grassmannian K m l) :
    Basis (projectedLatticeBasisIndex V) ℤ
      ((ambientIntegralRowModule (K := K) m) ⧸
        ambientKernelSubmodule (K := K) V) :=
  (projectedLatticeBasis V).map
    (ambientKernelQuotientEquivProjected V).symm

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  Combine the primitive lower-lattice basis and lifted
   projected-lattice basis.  `Module.Basis.sumQuot` supplies a genuine
   integral basis, so no complementary lattice is postulated. -/
noncomputable def ambientIntegralRowZBasis {m l : ℕ}
    (V : Grassmannian K m l) :
    Basis (rowLatticeBasisIndex V ⊕ projectedLatticeBasisIndex V) ℤ
      (ambientIntegralRowModule (K := K) m) :=
  Module.Basis.sumQuot (ambientKernelZBasis V)
    (ambientKernelQuotientBasis V)

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   The first block of the ambient basis is the primitive lower lattice. -/
theorem ambientIntegralRowZBasis_inl {m l : ℕ}
    (V : Grassmannian K m l) (i : rowLatticeBasisIndex V) :
    ambientIntegralRowZBasis V (Sum.inl i) =
      (ambientKernelZBasis V i : ambientIntegralRowModule (K := K) m) := by
  simp [ambientIntegralRowZBasis]

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   Modulo the lower lattice, the second block is exactly the chosen quotient
   basis. -/
theorem ambientIntegralRowZBasis_mkQ_inr {m l : ℕ}
    (V : Grassmannian K m l) (j : projectedLatticeBasisIndex V) :
    (ambientKernelSubmodule (K := K) V).mkQ
      (ambientIntegralRowZBasis V (Sum.inr j)) =
        ambientKernelQuotientBasis V j := by
  simp [ambientIntegralRowZBasis]

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   The projection of the second ambient block is the chosen projected-lattice
   basis.  This gives the lower-right block in the eventual determinant
   calculation directly in the manuscript's projected-lattice notation. -/
theorem ambientProjectedRowMap_ambientIntegralRowZBasis_inr {m l : ℕ}
    (V : Grassmannian K m l) (j : projectedLatticeBasisIndex V) :
    ambientProjectedRowMap V (ambientIntegralRowZBasis V (Sum.inr j)) =
      projectedLatticeBasis V j := by
  rw [← ambientKernelQuotientEquivProjected_apply_mk V]
  rw [ambientIntegralRowZBasis_mkQ_inr]
  simp [ambientKernelQuotientBasis]

noncomputable def rowProductZBasis {m k n : ℕ}
    (V : Grassmannian K m k) :
    Basis (Σ i : Fin n, rowLatticeBasisIndex V) ℤ
      (rowProductZLattice (n := n) V) :=
  (Pi.basis (fun _ : Fin n => rowLatticeBasis V)).map
    (rowProductZLatticeEquiv V).symm

noncomputable def rowOrthonormalBasis {m k : ℕ}
    (V : Grassmannian K m k) :
    OrthonormalBasis (rowLatticeBasisIndex V) ℝ (rowRealSpan V) :=
  (stdOrthonormalBasis ℝ (rowRealSpan V)).reindex
    (Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex ℤ
        (rowZLattice V), rowZLattice_finrank V, rowRealSpan_finrank V]))

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  The integral rank of the projected lattice agrees with the
   real dimension of the orthogonal complement.  This is the rank identity
   needed to choose a compatible orthonormal basis for its determinant. -/
theorem projectedLattice_finrank {m l : ℕ}
    (V : Grassmannian K m l) :
    Module.finrank ℤ (projectedAmbientRowModule (K := K) V) =
      Module.finrank ℝ ((rowRealSpan V)ᗮ) := by
  rw [ZLattice.rank (K := ℝ) (projectedAmbientRowModule (K := K) V)]

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  An orthonormal basis of the projected real space indexed by
   the projected integral lattice basis. -/
noncomputable def projectedOrthonormalBasis {m l : ℕ}
    (V : Grassmannian K m l) :
    OrthonormalBasis (projectedLatticeBasisIndex V) ℝ ((rowRealSpan V)ᗮ) :=
  (stdOrthonormalBasis ℝ ((rowRealSpan V)ᗮ)).reindex
    (Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex ℤ
        (projectedAmbientRowModule (K := K) V), projectedLattice_finrank V]))

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  Join orthonormal bases of the row space and its orthogonal
   complement through the verified orthogonal decomposition. -/
noncomputable def ambientOrthonormalBasis {m l : ℕ}
    (V : Grassmannian K m l) :
    OrthonormalBasis (rowLatticeBasisIndex V ⊕ projectedLatticeBasisIndex V) ℝ
      (RowVector K m) :=
  ((rowOrthonormalBasis V).prod (projectedOrthonormalBasis V)).map
    (rowRealSpan V).orthogonalDecomposition.symm

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  Regard the integral block basis as a real basis before taking
   its determinant against `ambientOrthonormalBasis`. -/
noncomputable def ambientIntegralRowRealBasis {m l : ℕ}
    (V : Grassmannian K m l) :
    Basis (rowLatticeBasisIndex V ⊕ projectedLatticeBasisIndex V) ℝ
      (RowVector K m) :=
  (ambientIntegralRowZBasis V).ofZLatticeBasis ℝ

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  The real basis associated to the projected integral lattice. -/
noncomputable def projectedRealBasis {m l : ℕ}
    (V : Grassmannian K m l) :
    Basis (projectedLatticeBasisIndex V) ℝ ((rowRealSpan V)ᗮ) :=
  (projectedLatticeBasis V).ofZLatticeBasis ℝ

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  The two basis-change maps whose determinants are the raw
   covolumes of the projected and ambient lattices. -/
noncomputable def projectedBasisChange {m l : ℕ}
    (V : Grassmannian K m l) :
    (rowRealSpan V)ᗮ ≃ₗ[ℝ] (rowRealSpan V)ᗮ :=
  (projectedOrthonormalBasis V).toBasis.equiv
    (projectedRealBasis V) (Equiv.refl _)

noncomputable def ambientBasisChange {m l : ℕ}
    (V : Grassmannian K m l) :
    RowVector K m ≃ₗ[ℝ] RowVector K m :=
  (ambientOrthonormalBasis V).toBasis.equiv
    (ambientIntegralRowRealBasis V) (Equiv.refl _)

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  Unfold the real bases back to their integral lattice vectors. -/
theorem ambientIntegralRowRealBasis_apply {m l : ℕ}
    (V : Grassmannian K m l)
    (q : rowLatticeBasisIndex V ⊕ projectedLatticeBasisIndex V) :
    ambientIntegralRowRealBasis V q =
      (ambientIntegralRowZBasis V q : RowVector K m) := by
  exact (ambientIntegralRowZBasis V).ofZLatticeBasis_apply ℝ
    (ambientIntegralRowModule (K := K) m) q

theorem projectedRealBasis_apply {m l : ℕ}
    (V : Grassmannian K m l) (j : projectedLatticeBasisIndex V) :
    projectedRealBasis V j =
      (projectedLatticeBasis V j : (rowRealSpan V)ᗮ) := by
  exact (projectedLatticeBasis V).ofZLatticeBasis_apply ℝ
    (projectedAmbientRowModule (K := K) V) j

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  Each basis-change map sends its chosen orthonormal basis to
   the corresponding real lattice basis. -/
theorem ambientBasisChange_apply_ambientOrthonormalBasis {m l : ℕ}
    (V : Grassmannian K m l)
    (q : rowLatticeBasisIndex V ⊕ projectedLatticeBasisIndex V) :
    ambientBasisChange V (ambientOrthonormalBasis V q) =
      ambientIntegralRowRealBasis V q := by
  exact Module.Basis.equiv_apply (ambientOrthonormalBasis V).toBasis q
    (ambientIntegralRowRealBasis V) (Equiv.refl _)

theorem projectedBasisChange_apply_projectedOrthonormalBasis {m l : ℕ}
    (V : Grassmannian K m l) (j : projectedLatticeBasisIndex V) :
    projectedBasisChange V (projectedOrthonormalBasis V j) =
      projectedRealBasis V j := by
  exact Module.Basis.equiv_apply (projectedOrthonormalBasis V).toBasis j
    (projectedRealBasis V) (Equiv.refl _)

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  The two index blocks of the ambient orthonormal basis are the
   row-space and orthogonal-complement bases, viewed in the ambient space. -/
theorem ambientOrthonormalBasis_apply_inl {m l : ℕ}
    (V : Grassmannian K m l) (i : rowLatticeBasisIndex V) :
    ambientOrthonormalBasis V (Sum.inl i) =
      ((rowOrthonormalBasis V i : rowRealSpan V) : RowVector K m) := by
  apply (rowRealSpan V).orthogonalDecomposition.injective
  simp [ambientOrthonormalBasis, OrthonormalBasis.prod_apply, Function.comp_def]

theorem ambientOrthonormalBasis_apply_inr {m l : ℕ}
    (V : Grassmannian K m l) (j : projectedLatticeBasisIndex V) :
    ambientOrthonormalBasis V (Sum.inr j) =
      ((projectedOrthonormalBasis V j : (rowRealSpan V)ᗮ) : RowVector K m) := by
  apply (rowRealSpan V).orthogonalDecomposition.injective
  simp [ambientOrthonormalBasis, OrthonormalBasis.prod_apply, Function.comp_def]

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   On the row-space block, the ambient basis change is exactly the basis
   change defining the primitive row-lattice covolume. -/
theorem ambientBasisChange_apply_rowOrthonormalBasis {m l : ℕ}
    (V : Grassmannian K m l) (i : rowLatticeBasisIndex V) :
    ambientBasisChange V ((rowOrthonormalBasis V i : rowRealSpan V) :
      RowVector K m) =
      ((rowLatticeBasis V i : rowZLattice V) : RowVector K m) := by
  rw [← ambientOrthonormalBasis_apply_inl V i]
  rw [ambientBasisChange_apply_ambientOrthonormalBasis]
  rw [ambientIntegralRowRealBasis_apply]
  rw [ambientIntegralRowZBasis_inl]
  exact ambientKernelZBasis_coe V i

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   On the projected block, orthogonally projecting the ambient basis change
   gives the projected-lattice basis change. -/
theorem projectedAmbientRowMap_ambientBasisChange_apply_projectedOrthonormalBasis
    {m l : ℕ} (V : Grassmannian K m l) (j : projectedLatticeBasisIndex V) :
    projectedAmbientRowMap V
      (ambientBasisChange V
        ((projectedOrthonormalBasis V j : (rowRealSpan V)ᗮ) : RowVector K m)) =
      projectedBasisChange V (projectedOrthonormalBasis V j) := by
  rw [← ambientOrthonormalBasis_apply_inr V j]
  rw [ambientBasisChange_apply_ambientOrthonormalBasis]
  rw [ambientIntegralRowRealBasis_apply]
  rw [projectedBasisChange_apply_projectedOrthonormalBasis]
  rw [projectedRealBasis_apply]
  have h := congrArg (fun z : projectedAmbientRowModule (K := K) V =>
    (z : (rowRealSpan V)ᗮ))
      (ambientProjectedRowMap_ambientIntegralRowZBasis_inr V j)
  simpa [ambientProjectedRowMap_apply] using h

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  The embedded row-space orthonormal basis spans exactly the
   row space in the ambient Minkowski vector space. -/
theorem rowRealSpan_eq_span_range_rowOrthonormalBasis {m l : ℕ}
    (V : Grassmannian K m l) :
    rowRealSpan V = Submodule.span ℝ
      (Set.range (fun i : rowLatticeBasisIndex V =>
        ((rowOrthonormalBasis V i : rowRealSpan V) : RowVector K m))) := by
  change rowRealSpan V = Submodule.span ℝ
    (Set.range ((rowRealSpan V).subtype ∘ rowOrthonormalBasis V))
  rw [Set.range_comp, Submodule.span_image]
  have hspan : Submodule.span ℝ
      (Set.range (rowOrthonormalBasis V :
        rowLatticeBasisIndex V → rowRealSpan V)) = ⊤ := by
    simpa using (rowOrthonormalBasis V).toBasis.span_eq
  rw [hspan, Submodule.map_subtype_top]

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   The ambient basis change preserves the lower row space.  This is precisely
   the zero lower-left block in the determinant calculation. -/
theorem ambientBasisChange_maps_rowRealSpan {m l : ℕ}
    (V : Grassmannian K m l) :
    rowRealSpan V ≤ (rowRealSpan V).comap
      (ambientBasisChange V).toLinearMap := by
  intro x hx
  change ambientBasisChange V x ∈ rowRealSpan V
  rw [rowRealSpan_eq_span_range_rowOrthonormalBasis V] at hx
  refine Submodule.span_induction
    (p := fun y _ => ambientBasisChange V y ∈ rowRealSpan V) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨i, rfl⟩
    rw [ambientBasisChange_apply_rowOrthonormalBasis]
    exact (rowLatticeBasis V i).1.property
  · simpa using (rowRealSpan V).zero_mem
  · intro y z _ _ hy hz
    simpa using (rowRealSpan V).add_mem hy hz
  · intro a y _ hy
    simpa using (rowRealSpan V).smul_mem a hy

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   The first real block is the primitive row-lattice basis in ambient
   coordinates. -/
theorem ambientIntegralRowZBasis_coe_inl {m l : ℕ}
    (V : Grassmannian K m l) (i : rowLatticeBasisIndex V) :
    ((ambientIntegralRowZBasis V (Sum.inl i) :
      ambientIntegralRowModule (K := K) m) : RowVector K m) =
      ((rowLatticeBasis V i : rowZLattice V) : RowVector K m) := by
  rw [ambientIntegralRowZBasis_inl]
  exact ambientKernelZBasis_coe V i

noncomputable def rowProductOrthonormalBasis {m k n : ℕ}
    (V : Grassmannian K m k) :
    OrthonormalBasis (Σ i : Fin n, rowLatticeBasisIndex V) ℝ
      (PiLp 2 (fun _ : Fin n => rowRealSpan V)) :=
  Pi.orthonormalBasis (fun _ => rowOrthonormalBasis V)

noncomputable def rowRealBasis {m k : ℕ} (V : Grassmannian K m k) :
    Basis (rowLatticeBasisIndex V) ℝ (rowRealSpan V) :=
  (rowLatticeBasis V).ofZLatticeBasis ℝ

noncomputable def rowProductRealBasis {m k n : ℕ}
    (V : Grassmannian K m k) :
    Basis (Σ i : Fin n, rowLatticeBasisIndex V) ℝ
      (PiLp 2 (fun _ : Fin n => rowRealSpan V)) :=
  (Pi.basis (fun _ : Fin n => rowRealBasis V)).map
    (WithLp.linearEquiv 2 ℝ (Fin n → rowRealSpan V)).symm

noncomputable def rowBasisChange {m k : ℕ} (V : Grassmannian K m k) :
    rowRealSpan V ≃ₗ[ℝ] rowRealSpan V :=
  (rowOrthonormalBasis V).toBasis.equiv (rowRealBasis V) (Equiv.refl _)

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   Restricting the ambient integral basis change to the lower row space gives
   exactly the basis change whose determinant is `H(D')`. -/
theorem ambientBasisChange_restrict_eq_rowBasisChange {m l : ℕ}
    (V : Grassmannian K m l) :
    (ambientBasisChange V).toLinearMap.restrict
        (ambientBasisChange_maps_rowRealSpan V) =
      (rowBasisChange V).toLinearMap := by
  apply (rowOrthonormalBasis V).toBasis.ext
  intro i
  apply Subtype.ext
  change ambientBasisChange V
      ((rowOrthonormalBasis V i : rowRealSpan V) : RowVector K m) =
    ((rowBasisChange V (rowOrthonormalBasis V i) : rowRealSpan V) : RowVector K m)
  rw [ambientBasisChange_apply_rowOrthonormalBasis]
  rw [show rowBasisChange V =
      (rowOrthonormalBasis V).toBasis.equiv (rowRealBasis V) (Equiv.refl _) by
        rfl]
  have hbasis : rowOrthonormalBasis V i =
      (rowOrthonormalBasis V).toBasis i := rfl
  rw [hbasis]
  rw [Module.Basis.equiv_apply]
  simpa [rowRealBasis] using congrArg
    (fun z : rowRealSpan V => (z : RowVector K m))
    ((rowLatticeBasis V).ofZLatticeBasis_apply ℝ (rowZLattice V) i).symm

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  Identify the real quotient by the lower row space with its
   orthogonal complement using the same projection occurring in the
   manuscript's projected lattice. -/
noncomputable def rowSpaceQuotientEquivProjection {m l : ℕ}
    (V : Grassmannian K m l) :
    (RowVector K m ⧸ rowRealSpan V) ≃ₗ[ℝ] (rowRealSpan V)ᗮ :=
  (rowRealSpan V).quotientEquivOfIsCompl (rowRealSpan V)ᗮ
    (rowRealSpan V).isCompl_orthogonal

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   This quotient identification composed with the quotient map is the
   manuscript's orthogonal projection. -/
theorem rowSpaceQuotientEquivProjection_comp_mkQ {m l : ℕ}
    (V : Grassmannian K m l) :
    (rowSpaceQuotientEquivProjection V).toLinearMap.comp
        (rowRealSpan V).mkQ =
      ((rowRealSpan V)ᗮ.orthogonalProjectionOnto).toLinearMap := by
  rw [rowSpaceQuotientEquivProjection]
  rw [Submodule.quotientEquivOfIsCompl_comp_mkQ]
  ext x
  obtain ⟨u, v, huv, _⟩ :=
    Submodule.existsUnique_add_of_isCompl
      (rowRealSpan V).isCompl_orthogonal x
  rw [← huv]
  have huperp : (u : RowVector K m) ∈ (rowRealSpan V)ᗮᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal' (rowRealSpan V) w).mp hw u u.property
  have hleft : (rowRealSpan V)ᗮ.projectionOnto (rowRealSpan V)
      (rowRealSpan V).isCompl_orthogonal.symm (u : RowVector K m) = 0 := by
    exact Submodule.projectionOnto_apply_right
      (rowRealSpan V).isCompl_orthogonal.symm u
  have hright : (rowRealSpan V)ᗮ.projectionOnto (rowRealSpan V)
      (rowRealSpan V).isCompl_orthogonal.symm (v : RowVector K m) = v := by
    exact Submodule.projectionOnto_apply_left
      (rowRealSpan V).isCompl_orthogonal.symm v
  have horthoLeft : (rowRealSpan V)ᗮ.orthogonalProjectionOnto
      (u : RowVector K m) = 0 := by
    rw [Submodule.orthogonalProjectionOnto_apply_eq_projectionOnto]
    exact Submodule.projectionOnto_apply_right
      ((rowRealSpan V)ᗮ).isCompl_orthogonal ⟨u, huperp⟩
  have horthoRight : (rowRealSpan V)ᗮ.orthogonalProjectionOnto
      (v : RowVector K m) = v := by
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v
  simp [map_add, hleft, hright, horthoLeft, horthoRight]

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   Pointwise form of the preceding bridge, expressed in the projected-lattice
   notation already used by the rest of the development. -/
theorem rowSpaceQuotientEquivProjection_apply_mkQ {m l : ℕ}
    (V : Grassmannian K m l) (x : RowVector K m) :
    rowSpaceQuotientEquivProjection V ((rowRealSpan V).mkQ x) =
      projectedAmbientRowMap V x := by
  have h := LinearMap.congr_fun
    (rowSpaceQuotientEquivProjection_comp_mkQ V) x
  exact h

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  The endomorphism induced by the ambient integral basis change
   on the quotient by the lower row space. -/
noncomputable def ambientBasisChangeQuotient {m l : ℕ}
    (V : Grassmannian K m l) :
    (RowVector K m ⧸ rowRealSpan V) →ₗ[ℝ] (RowVector K m ⧸ rowRealSpan V) :=
  (rowRealSpan V).mapQ (rowRealSpan V) (ambientBasisChange V).toLinearMap
    (ambientBasisChange_maps_rowRealSpan V)

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   Conjugating the quotient action by the projection identification gives the
   projected-lattice basis change.  This identifies the lower-right block in
   the manuscript's determinant calculation. -/
theorem rowSpaceQuotientEquivProjection_conj_ambientBasisChangeQuotient
    {m l : ℕ} (V : Grassmannian K m l) :
    (rowSpaceQuotientEquivProjection V).conj
      (ambientBasisChangeQuotient V) =
        (projectedBasisChange V).toLinearMap := by
  apply (projectedOrthonormalBasis V).toBasis.ext
  intro j
  rw [LinearEquiv.conj_apply_apply]
  have hbasis : (projectedOrthonormalBasis V).toBasis j =
      projectedOrthonormalBasis V j := rfl
  rw [hbasis]
  have hsymm : (rowSpaceQuotientEquivProjection V).symm
      (projectedOrthonormalBasis V j) =
        (rowRealSpan V).mkQ
          ((projectedOrthonormalBasis V j : (rowRealSpan V)ᗮ) : RowVector K m) := by
    apply (rowSpaceQuotientEquivProjection V).injective
    rw [LinearEquiv.apply_symm_apply]
    rw [rowSpaceQuotientEquivProjection_apply_mkQ]
    exact (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (projectedOrthonormalBasis V j)).symm
  rw [hsymm]
  rw [ambientBasisChangeQuotient]
  rw [Submodule.mkQ_apply, Submodule.mapQ_apply]
  rw [← Submodule.mkQ_apply]
  rw [rowSpaceQuotientEquivProjection_apply_mkQ]
  exact projectedAmbientRowMap_ambientBasisChange_apply_projectedOrthonormalBasis V j

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   Determinants are invariant under the preceding quotient conjugation. -/
theorem ambientBasisChangeQuotient_det_eq_projectedBasisChange_det {m l : ℕ}
    (V : Grassmannian K m l) :
    LinearMap.det (ambientBasisChangeQuotient V) =
      LinearMap.det (projectedBasisChange V).toLinearMap := by
  rw [← rowSpaceQuotientEquivProjection_conj_ambientBasisChangeQuotient V]
  exact (LinearMap.det_conj (ambientBasisChangeQuotient V)
    (rowSpaceQuotientEquivProjection V)).symm

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   The ambient determinant factors into the lower primitive-row block and
   the projected quotient block. -/
theorem ambientBasisChange_det_eq_rowBasisChange_det_mul_projectedBasisChange_det
    {m l : ℕ} (V : Grassmannian K m l) :
    LinearMap.det (ambientBasisChange V).toLinearMap =
      LinearMap.det (rowBasisChange V).toLinearMap *
        LinearMap.det (projectedBasisChange V).toLinearMap := by
  rw [LinearMap.det_eq_det_mul_det (rowRealSpan V)
    (ambientBasisChange V).toLinearMap
    (ambientBasisChange_maps_rowRealSpan V)]
  rw [ambientBasisChange_restrict_eq_rowBasisChange]
  change LinearMap.det (rowBasisChange V).toLinearMap *
      LinearMap.det (ambientBasisChangeQuotient V) =
    LinearMap.det (rowBasisChange V).toLinearMap *
      LinearMap.det (projectedBasisChange V).toLinearMap
  rw [ambientBasisChangeQuotient_det_eq_projectedBasisChange_det]

noncomputable def rowProductBasisChange {m k n : ℕ}
    (V : Grassmannian K m k) :
    PiLp 2 (fun _ : Fin n => rowRealSpan V) ≃ₗ[ℝ]
      PiLp 2 (fun _ : Fin n => rowRealSpan V) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → rowRealSpan V)).trans
    ((LinearEquiv.piCongrRight (fun _ : Fin n => rowBasisChange V)).trans
      (WithLp.linearEquiv 2 ℝ (Fin n → rowRealSpan V)).symm)

theorem rowBasisChange_det {m k : ℕ} (V : Grassmannian K m k) :
    LinearMap.det (rowBasisChange V).toLinearMap =
      (rowOrthonormalBasis V).toBasis.det (rowRealBasis V) := by
  simpa [rowBasisChange] using
    (Module.Basis.det_basis (rowRealBasis V)
      (rowOrthonormalBasis V).toBasis)

theorem rowProductBasisChange_eq_basisEquiv {m k n : ℕ}
    (V : Grassmannian K m k) :
    rowProductBasisChange (n := n) V =
      (rowProductOrthonormalBasis (n := n) V).toBasis.equiv
        (rowProductRealBasis (n := n) V)
        (Equiv.refl _) := by
  simp only [rowProductOrthonormalBasis, Pi.orthonormalBasis.toBasis,
    rowProductRealBasis]
  apply ((Pi.basis (fun _ : Fin n => (rowOrthonormalBasis V).toBasis)).map
    (WithLp.linearEquiv 2 ℝ (Fin n → rowRealSpan V)).symm).ext'
  rintro ⟨i, j⟩
  rw [Basis.equiv_apply]
  simp [rowProductBasisChange, rowBasisChange]
  apply PiLp.ext
  intro l
  by_cases h : l = i
  · subst l
    simpa [rowRealBasis] using
      (Module.Basis.equiv_apply (rowOrthonormalBasis V).toBasis j
        (rowRealBasis V) (Equiv.refl _))
  · simp [rowBasisChange, rowRealBasis, h]

theorem rowProductBasisChange_det {m k n : ℕ}
    (V : Grassmannian K m k) :
    LinearMap.det (rowProductBasisChange (n := n) V).toLinearMap =
      ∏ i : Fin n, LinearMap.det (rowBasisChange V).toLinearMap := by
  let p : (Fin n → rowRealSpan V) ≃ₗ[ℝ] (Fin n → rowRealSpan V) :=
    LinearEquiv.piCongrRight (fun _ : Fin n => rowBasisChange V)
  have hp : p.toLinearMap =
      LinearMap.pi (fun i : Fin n =>
        (rowBasisChange V).toLinearMap.comp (LinearMap.proj i)) := by
    ext x i
    rfl
  have hdet : LinearEquiv.det (rowProductBasisChange (n := n) V) =
      LinearEquiv.det p := by
    have hcomp : rowProductBasisChange (n := n) V =
        ((WithLp.linearEquiv 2 ℝ (Fin n → rowRealSpan V)).trans p).trans
          (WithLp.linearEquiv 2 ℝ (Fin n → rowRealSpan V)).symm := by
      ext x
      rfl
    rw [hcomp]
    exact LinearEquiv.det_conj p
      (WithLp.linearEquiv 2 ℝ (Fin n → rowRealSpan V)).symm
  have hdet' := congrArg (fun u : ℝˣ => (u : ℝ)) hdet
  rw [LinearEquiv.coe_det, LinearEquiv.coe_det] at hdet'
  rw [hp, LinearMap.det_pi] at hdet'
  exact hdet'

theorem rowProductZBasis_coe_eq_rowProductRealBasis {m k n : ℕ}
    (V : Grassmannian K m k) :
    (fun i => ((rowProductZBasis (n := n) V i : rowProductZLattice (n := n) V) :
      PiLp 2 (fun _ : Fin n => rowRealSpan V))) =
        rowProductRealBasis (n := n) V := by
  funext i
  rcases i with ⟨i, j⟩
  simp [rowProductZBasis, rowProductRealBasis, rowProductZLatticeEquiv,
    rowRealBasis]
  rw [PiLp.single]
  congr 1
  funext l
  by_cases h : l = i <;> simp [h]

set_option maxHeartbeats 5000000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem rowProductOrthonormalBasis_fundamentalDomain_measureReal {m k n : ℕ}
    (V : Grassmannian K m k) :
    (μHE[Module.finrank ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V))] :
      Measure (PiLp 2 (fun _ : Fin n => rowRealSpan V))).real
        (ZSpan.fundamentalDomain (rowProductOrthonormalBasis (n := n) V).toBasis) = 1 := by
  have hμ : (μHE[Module.finrank ℝ
      (PiLp 2 (fun _ : Fin n => rowRealSpan V))] :
      Measure (PiLp 2 (fun _ : Fin n => rowRealSpan V))) = volume :=
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  rw [hμ]
  rw [measureReal_congr
    (ZSpan.fundamentalDomain_ae_parallelepiped
      (rowProductOrthonormalBasis (n := n) V).toBasis volume)]
  simp [MeasureTheory.measureReal_def,
    (rowProductOrthonormalBasis (n := n) V).volume_parallelepiped]

theorem rowOrthonormalBasis_fundamentalDomain_measureReal {m k : ℕ}
    (V : Grassmannian K m k) :
    (μHE[Module.finrank ℝ (rowRealSpan V)] : Measure (rowRealSpan V)).real
        (ZSpan.fundamentalDomain (rowOrthonormalBasis V).toBasis) = 1 := by
  have hμ : (μHE[Module.finrank ℝ (rowRealSpan V)] :
      Measure (rowRealSpan V)) = volume :=
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  rw [hμ]
  rw [measureReal_congr
    (ZSpan.fundamentalDomain_ae_parallelepiped
      (rowOrthonormalBasis V).toBasis volume)]
  simp [MeasureTheory.measureReal_def,
    (rowOrthonormalBasis V).volume_parallelepiped]

theorem rowSpaceHeight_eq_rowBasisChange_det_abs {m k : ℕ}
    (V : Grassmannian K m k) :
    rowSpaceHeight V = |LinearMap.det (rowBasisChange V).toLinearMap| := by
  rw [rowSpaceHeight,
    ZLattice.covolume_eq_det_mul_measureReal (rowZLattice V)
      (μHE[Module.finrank ℝ (rowRealSpan V)]) (rowLatticeBasis V)
      (rowOrthonormalBasis V).toBasis,
    rowOrthonormalBasis_fundamentalDomain_measureReal V, mul_one]
  rw [rowBasisChange_det]
  have hvec : (Subtype.val ∘ ⇑(rowLatticeBasis V)) =
      ⇑(rowRealBasis V) := by
    funext i
    simp [rowRealBasis]
  rw [hvec]

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  The orthogonal-complement subtype needs its canonical Borel
   structure explicitly when its covolume is expressed through a fundamental
   domain. -/
noncomputable local instance rowLatticeProjectedRowMeasurableSpace {m l : ℕ}
    (V : Grassmannian K m l) :
    MeasurableSpace ((rowRealSpan V)ᗮ) := borel ((rowRealSpan V)ᗮ)

local instance rowLatticeProjectedRowBorelSpace {m l : ℕ}
    (V : Grassmannian K m l) :
    BorelSpace ((rowRealSpan V)ᗮ) := ⟨rfl⟩

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  Fundamental domains of the compatible ambient and projected
   orthonormal bases have Euclidean measure one. -/
theorem ambientOrthonormalBasis_fundamentalDomain_measureReal {m l : ℕ}
    (V : Grassmannian K m l) :
    (μHE[Module.finrank ℝ (RowVector K m)] : Measure (RowVector K m)).real
      (ZSpan.fundamentalDomain (ambientOrthonormalBasis V).toBasis) = 1 := by
  have hμ : (μHE[Module.finrank ℝ (RowVector K m)] :
      Measure (RowVector K m)) = volume :=
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  rw [hμ]
  rw [measureReal_congr
    (ZSpan.fundamentalDomain_ae_parallelepiped
      (ambientOrthonormalBasis V).toBasis volume)]
  simp [MeasureTheory.measureReal_def,
    (ambientOrthonormalBasis V).volume_parallelepiped]

theorem projectedOrthonormalBasis_fundamentalDomain_measureReal {m l : ℕ}
    (V : Grassmannian K m l) :
    (μHE[Module.finrank ℝ ((rowRealSpan V)ᗮ)] :
      Measure ((rowRealSpan V)ᗮ)).real
      (ZSpan.fundamentalDomain (projectedOrthonormalBasis V).toBasis) = 1 := by
  have hμ : (μHE[Module.finrank ℝ ((rowRealSpan V)ᗮ)] :
      Measure ((rowRealSpan V)ᗮ)) = volume :=
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  rw [hμ]
  rw [measureReal_congr
    (ZSpan.fundamentalDomain_ae_parallelepiped
      (projectedOrthonormalBasis V).toBasis volume)]
  simp [MeasureTheory.measureReal_def,
    (projectedOrthonormalBasis V).volume_parallelepiped]

/- [Lean infrastructure, used for paper `le:low_rank_induction`, lines
   1475--1479]  Determinants of the ambient and projected basis changes in
   their compatible orthonormal coordinates. -/
set_option maxHeartbeats 5000000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem ambientBasisChange_det {m l : ℕ} (V : Grassmannian K m l) :
    LinearMap.det (ambientBasisChange V).toLinearMap =
      (ambientOrthonormalBasis V).toBasis.det (ambientIntegralRowRealBasis V) := by
  simpa [ambientBasisChange] using
    (Module.Basis.det_basis (ambientIntegralRowRealBasis V)
      (ambientOrthonormalBasis V).toBasis)

set_option maxHeartbeats 5000000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem projectedBasisChange_det {m l : ℕ} (V : Grassmannian K m l) :
    LinearMap.det (projectedBasisChange V).toLinearMap =
      (projectedOrthonormalBasis V).toBasis.det (projectedRealBasis V) := by
  simpa [projectedBasisChange] using
    (Module.Basis.det_basis (projectedRealBasis V)
      (projectedOrthonormalBasis V).toBasis)

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   The following are covolume identities in Mathlib's raw Euclidean metric.
   They are intentionally kept separate from the paper-normalized measure;
   the explicit metric-conversion bridge is still required before using them
   as the manuscript's displayed `H(D')⁻¹` identity. -/
set_option maxHeartbeats 5000000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem ambientIntegralRowModule_covolume_eq_ambientBasisChange_det_abs
    {m l : ℕ} (V : Grassmannian K m l) :
    ZLattice.covolume (ambientIntegralRowModule (K := K) m)
      (μHE[Module.finrank ℝ (RowVector K m)]) =
        |LinearMap.det (ambientBasisChange V).toLinearMap| := by
  rw [ZLattice.covolume_eq_det_mul_measureReal
    (ambientIntegralRowModule (K := K) m)
    (μHE[Module.finrank ℝ (RowVector K m)])
    (ambientIntegralRowZBasis V)
    (ambientOrthonormalBasis V).toBasis,
    ambientOrthonormalBasis_fundamentalDomain_measureReal V, mul_one]
  rw [ambientBasisChange_det]
  have hvec : (Subtype.val ∘ ⇑(ambientIntegralRowZBasis V)) =
      ⇑(ambientIntegralRowRealBasis V) := by
    funext q
    rw [ambientIntegralRowRealBasis_apply]
    rfl
  rw [hvec]

set_option maxHeartbeats 5000000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem projectedAmbientRowModule_covolume_eq_projectedBasisChange_det_abs
    {m l : ℕ} (V : Grassmannian K m l) :
    ZLattice.covolume (projectedAmbientRowModule (K := K) V)
      (μHE[Module.finrank ℝ ((rowRealSpan V)ᗮ)]) =
        |LinearMap.det (projectedBasisChange V).toLinearMap| := by
  rw [ZLattice.covolume_eq_det_mul_measureReal
    (projectedAmbientRowModule (K := K) V)
    (μHE[Module.finrank ℝ ((rowRealSpan V)ᗮ)])
    (projectedLatticeBasis V)
    (projectedOrthonormalBasis V).toBasis,
    projectedOrthonormalBasis_fundamentalDomain_measureReal V, mul_one]
  rw [projectedBasisChange_det]
  have hvec : (Subtype.val ∘ ⇑(projectedLatticeBasis V)) =
      ⇑(projectedRealBasis V) := by
    funext j
    rw [projectedRealBasis_apply]
    rfl
  rw [hvec]

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   Raw-metric form of the primitive projection formula.  It is the exact
   determinant computation behind the manuscript's projected-lattice step,
   before the separately recorded conversion to the manuscript metric. -/
set_option maxHeartbeats 5000000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem ambientIntegralRowModule_covolume_eq_rowSpaceHeight_mul_projectedCovolume
    {m l : ℕ} (V : Grassmannian K m l) :
    ZLattice.covolume (ambientIntegralRowModule (K := K) m)
      (μHE[Module.finrank ℝ (RowVector K m)]) =
    rowSpaceHeight V *
      ZLattice.covolume (projectedAmbientRowModule (K := K) V)
        (μHE[Module.finrank ℝ ((rowRealSpan V)ᗮ)]) := by
  rw [ambientIntegralRowModule_covolume_eq_ambientBasisChange_det_abs,
    projectedAmbientRowModule_covolume_eq_projectedBasisChange_det_abs,
    rowSpaceHeight_eq_rowBasisChange_det_abs,
    ambientBasisChange_det_eq_rowBasisChange_det_mul_projectedBasisChange_det,
    abs_mul]

theorem rowProductOrthonormalBasis_det_rowProductRealBasis {m k n : ℕ}
    (V : Grassmannian K m k) :
    (rowProductOrthonormalBasis (n := n) V).toBasis.det
        (rowProductRealBasis (n := n) V) =
      ∏ i : Fin n, LinearMap.det (rowBasisChange V).toLinearMap := by
  rw [← Module.Basis.det_basis (rowProductRealBasis (n := n) V)
    (rowProductOrthonormalBasis (n := n) V).toBasis]
  rw [← rowProductBasisChange_eq_basisEquiv (n := n) V]
  exact rowProductBasisChange_det (n := n) V

set_option maxHeartbeats 5000000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem rowProductZLattice_covolume_eq_rowSpaceHeight_pow {m k n : ℕ}
    (V : Grassmannian K m k) :
    ZLattice.covolume (rowProductZLattice (n := n) V)
        (μHE[Module.finrank ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V))]) =
      (rowSpaceHeight V) ^ n := by
  rw [ZLattice.covolume_eq_det_mul_measureReal
      (rowProductZLattice (n := n) V)
      (μHE[Module.finrank ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V))])
      (rowProductZBasis (n := n) V)
      (rowProductOrthonormalBasis (n := n) V).toBasis,
    rowProductOrthonormalBasis_fundamentalDomain_measureReal (n := n) V, mul_one]
  have hcoe : ((↑) ∘ rowProductZBasis (n := n) V) =
      rowProductRealBasis (n := n) V := by
    simpa [Function.comp_def] using
      rowProductZBasis_coe_eq_rowProductRealBasis (n := n) V
  rw [hcoe, rowProductOrthonormalBasis_det_rowProductRealBasis (n := n) V,
    Finset.abs_prod]
  simp_rw [← rowSpaceHeight_eq_rowBasisChange_det_abs V]
  simp [Fintype.card_fin]

set_option maxHeartbeats 5000000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem rowProductZLattice_covolume_eq_rowMatrixZLattice_covolume {m k n : ℕ}
    (V : Grassmannian K m k) :
    ZLattice.covolume (rowProductZLattice (n := n) V)
      (μHE[Module.finrank ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V))]) =
      ZLattice.covolume (rowMatrixZLattice V n)
        (rowMatrixEuclideanMeasure (n := n) V) := by
  rw [rowProductZLattice_eq_comap (n := n) V]
  let hdim : Module.finrank ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V)) =
      Module.finrank ℝ (rowMatrixRealSpan V n) := by
    calc
      Module.finrank ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V)) =
          Module.finrank ℝ (Fin n → rowRealSpan V) :=
        (WithLp.linearEquiv 2 ℝ (Fin n → rowRealSpan V)).finrank_eq
      _ = Module.finrank ℝ (rowMatrixRealSpan V n) := by
        rw [Module.finrank_pi_fintype ℝ, rowMatrixRealSpan_finrank V]
        simp [rowRealSpan_finrank]
  let msW : MeasurableSpace (rowMatrixRealSpan V n) :=
    @Subtype.instMeasurableSpace (M n m (K_ℝ[K]))
      (fun A => A ∈ rowMatrixRealSpan V n)
      (kRealMatrixMeasurableSpace (K := K))
  let bsW : @BorelSpace (rowMatrixRealSpan V n) inferInstance msW :=
    @Subtype.borelSpace (M n m (K_ℝ[K])) inferInstance
      (kRealMatrixMeasurableSpace (K := K))
      (kRealMatrixBorelSpace (K := K))
      (fun A => A ∈ rowMatrixRealSpan V n)
  letI : MeasurableSpace (rowMatrixRealSpan V n) := msW
  letI : BorelSpace (rowMatrixRealSpan V n) := bsW
  let nsgW : NormedAddCommGroup (rowMatrixRealSpan V n) := inferInstance
  let nspW : NormedSpace ℝ (rowMatrixRealSpan V n) := inferInstance
  let fdW : FiniteDimensional ℝ (rowMatrixRealSpan V n) := inferInstance
  let nsgF : NormedAddCommGroup (PiLp 2 (fun _ : Fin n => rowRealSpan V)) :=
    inferInstance
  let nspF : NormedSpace ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V)) :=
    inferInstance
  let fdF : FiniteDimensional ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V)) :=
    inferInstance
  letI : NormedAddCommGroup (rowMatrixRealSpan V n) := nsgW
  letI : NormedSpace ℝ (rowMatrixRealSpan V n) := nspW
  letI : NormedAddCommGroup (PiLp 2 (fun _ : Fin n => rowRealSpan V)) := nsgF
  letI : NormedSpace ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V)) := nspF
  have hhaarW := @MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure
    (rowMatrixRealSpan V n) nsgW nspW fdW msW bsW
  have hmp :=
    @IsometryEquiv.measurePreserving_euclideanHausdorffMeasure
      (PiLp 2 (fun _ : Fin n => rowRealSpan V))
      (rowMatrixRealSpan V n)
      inferInstance inferInstance inferInstance inferInstance msW bsW
      (rowMatrixRealSpanLpIsometryEquiv (n := n) V).symm.toIsometryEquiv
      (Module.finrank ℝ (rowMatrixRealSpan V n))
  have hhaarF :
      (@Measure.euclideanHausdorffMeasure
        (PiLp 2 (fun _ : Fin n => rowRealSpan V)) inferInstance inferInstance
        inferInstance (Module.finrank ℝ (rowMatrixRealSpan V n))).IsAddHaarMeasure := by
    simpa [hdim] using
      (@MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure
        (PiLp 2 (fun _ : Fin n => rowRealSpan V)) inferInstance inferInstance
        inferInstance inferInstance inferInstance)
  have hcov := @ZLattice.covolume_comap
    (rowMatrixRealSpan V n)
    nsgW nspW fdW msW bsW
    (rowMatrixZLattice V n)
    (rowMatrixZLattice_discreteTopology V)
    (rowMatrixZLattice.isZLattice V)
    (rowMatrixEuclideanMeasure (n := n) V)
    hhaarW
    (PiLp 2 (fun _ : Fin n => rowRealSpan V))
    nsgF nspF fdF inferInstance inferInstance
    (μHE[Module.finrank ℝ (rowMatrixRealSpan V n)])
    hhaarF
  rw [hdim]
  exact hcov
    (e := (rowMatrixRealSpanLpIsometryEquiv (n := n) V).symm.toContinuousLinearEquiv)
    hmp

/- [derived consequence, paper `le:without_rank_cond`, lines 1038--1040]
   The exact covolume identity for the matrix realization of `M_n(Λ_D)`. -/
theorem rowMatrixZLattice_covolume_eq_rowSpaceHeight_pow {m k n : ℕ}
    (V : Grassmannian K m k) :
    ZLattice.covolume (rowMatrixZLattice V n)
        (rowMatrixEuclideanMeasure (n := n) V) =
      (rowSpaceHeight V) ^ n := by
  calc
    ZLattice.covolume (rowMatrixZLattice V n)
        (rowMatrixEuclideanMeasure (n := n) V) =
        ZLattice.covolume (rowProductZLattice (n := n) V)
          (μHE[Module.finrank ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V))]) :=
      (rowProductZLattice_covolume_eq_rowMatrixZLattice_covolume V).symm
    _ = (rowSpaceHeight V) ^ n :=
      rowProductZLattice_covolume_eq_rowSpaceHeight_pow V

/- The integral matrix lattice is the finite product of the corresponding
   one-row lattices.  This is the algebraic part of the product-covolume
   observation in Lemma `le:without_rank_cond`. -/
noncomputable def rowMatrixZLatticeEquiv {m k n : ℕ}
    (V : Grassmannian K m k) :
    rowMatrixZLattice V n ≃ₗ[ℤ] (Fin n → rowZLattice V) := by
  let e : rowMatrixZLattice V n ≃ₗ[ℤ] (Fin n → rowZLattice V) := {
    toFun := fun A i =>
      ⟨⟨rowVectorOfFun (A.1.1 i), by
          have hA : (A.1.1 : M n m (K_ℝ[K])) ∈ rowMatrixRealSpan V n := A.1.2
          have hEq := congrArg
            (fun W : Submodule ℝ (M n m (K_ℝ[K])) =>
              (A.1.1 : M n m (K_ℝ[K])) ∈ W)
            (rowMatrixRealSpan_eq_rowwise (n := n) V)
          have hA' : (A.1.1 : M n m (K_ℝ[K])) ∈
              rowMatrixRowwiseSubmodule V := hEq.mp hA
          exact (mem_rowMatrixRowwiseSubmodule_iff V _).mp hA' i⟩,
        by
          change rowVectorOfFun ((A.1.1 : M n m (K_ℝ[K])) i) ∈
            embeddedIntegralRowModule V
          exact (mem_embeddedRowMatrixModule_iff_rows V
            (A.1.1 : M n m (K_ℝ[K]))).1 A.2 i⟩
    invFun := fun A =>
      let b : M n m (K_ℝ[K]) := fun i => (A i).1.1.ofLp
      ⟨⟨b, by
          rw [rowMatrixRealSpan_eq_rowwise (n := n) V]
          intro i
          simpa [b] using (A i).1.2⟩,
        by
          change b ∈ embeddedRowMatrixModule V n
          rw [mem_embeddedRowMatrixModule_iff_rows V b]
          intro i
          have hi : (A i).1 ∈ rowZLattice V := (A i).2
          change rowVectorOfFun ((A i).1.1.ofLp) ∈
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
    rowMatrixZLattice.discreteTopology (n := n) V
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
    (rowMatrixZLattice.discreteTopology (n := n) V) p
    (by simpa [rowMatrixZLattice_finrank V] using hgap)

@[simp]
theorem rowMatrixZLatticeEquiv_coe {m k n : ℕ}
    (V : Grassmannian K m k) (A : rowMatrixZLattice V n) (i : Fin n) :
    (((rowMatrixZLatticeEquiv V A i : rowZLattice V) : rowRealSpan V) :
      RowVector K m) =
      ((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K])) i := by
  apply congrArg WithLp.ofLp
  rfl

/- [Lean infrastructure] Norm form of the preceding row-coordinate bridge.
   This packages the harmless subtype/Frobenius bookkeeping separately from
   the manuscript-facing successive-minimum argument. -/
theorem rowMatrixZLatticeEquiv_norm_coe {m k n : ℕ}
    (V : Grassmannian K m k) (A : rowMatrixZLattice V n) (i : Fin n) :
    ‖((rowMatrixZLatticeEquiv V A i : rowZLattice V) : rowRealSpan V)‖ =
      ‖rowVectorOfFun
        (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K])) i)‖ := by
  change ‖(((rowMatrixZLatticeEquiv V A i : rowZLattice V) :
    rowRealSpan V) : RowVector K m)‖ = _
  have hrow := rowMatrixZLatticeEquiv_coe V A i
  have hrowvec :
      (((rowMatrixZLatticeEquiv V A i : rowZLattice V) :
        rowRealSpan V) : RowVector K m) =
        rowVectorOfFun
          (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K])) i) := by
    apply PiLp.ext
    intro j
    exact congrFun hrow j
  exact congrArg norm hrowvec

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

theorem rowMatrixRank_eq_zero_iff {m k n : ℕ}
    (V : Grassmannian K m k) (A : rowMatrixZLattice V n) :
    rowMatrixRank V A = 0 ↔ A = 0 := by
  let e := integralRowMatricesEquivRowMatrixZLattice V n
  have hzeroRows : rowsInIntegralRowModule V (0 : IntegralMatrix K n m) := by
    intro i
    exact (integralRowModule V).zero_mem
  let zeroRows : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A} :=
    ⟨0, hzeroRows⟩
  have hezero : e zeroRows = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [integralRowMatricesEquivRowMatrixZLattice_coe]
    ext i j
    simp [zeroRows, embedMatrix]
  constructor
  · intro hA
    have hzero : (e.symm A).1 = 0 :=
      integralMatrix_eq_zero_of_integralMatrixRank_eq_zero
        (e.symm A).1 hA
    have heq : e.symm A = zeroRows := Subtype.ext hzero
    calc
      A = e (e.symm A) := (e.apply_symm_apply A).symm
      _ = e zeroRows := by rw [heq]
      _ = 0 := hezero
  · intro hA
    subst A
    have hzero : (e.symm (0 : rowMatrixZLattice V n)).1 = 0 := by
      apply integralMatrixEmbedding_injective (K := K) n m
      change embedMatrix (e.symm (0 : rowMatrixZLattice V n)).1 =
        embedMatrix (0 : IntegralMatrix K n m)
      have h := congrArg (fun C : rowMatrixZLattice V n =>
        ((C : rowMatrixRealSpan V n) : M n m (K_ℝ[K])))
        (e.apply_symm_apply (0 : rowMatrixZLattice V n))
      rw [integralRowMatricesEquivRowMatrixZLattice_coe] at h
      rw [show embedMatrix (0 : IntegralMatrix K n m) = 0 by
        ext i j
        simp [embedMatrix]]
      exact h
    have heq : e.symm (0 : rowMatrixZLattice V n) = zeroRows :=
      Subtype.ext hzero
    change integralMatrixRank (e.symm (0 : rowMatrixZLattice V n)).1 = 0
    rw [heq]
    change Matrix.rank (algebraicMatrix (0 : IntegralMatrix K n m)) = 0
    rw [show algebraicMatrix (0 : IntegralMatrix K n m) = 0 by
      ext i j
      simp [algebraicMatrix]]
    exact Matrix.rank_zero

theorem rowMatrixRank_pos_iff {m k n : ℕ}
    (V : Grassmannian K m k) (A : rowMatrixZLattice V n) :
    0 < rowMatrixRank V A ↔ A ≠ 0 := by
  rw [Nat.pos_iff_ne_zero]
  constructor
  · intro hA hzero
    apply hA
    rw [hzero, rowMatrixRank_eq_zero_iff]
  · intro hne hzero
    apply hne
    exact (rowMatrixRank_eq_zero_iff V A).1 hzero

theorem rowMatrixRank_eq_iff_rowSpace_eq {m k n : ℕ}
    (V : Grassmannian K m k) (A : rowMatrixZLattice V n) :
    rowMatrixRank V A = k ↔
      matrixRowSpace ((integralRowMatricesEquivRowMatrixZLattice V n).symm A).1 = V.1 := by
  let B := (integralRowMatricesEquivRowMatrixZLattice V n).symm A
  change integralMatrixRank B.1 = k ↔ matrixRowSpace B.1 = V.1
  exact (rowSpace_eq_iff_rank_eq_of_rowsIn V B.1 B.2).symm

/- [paper, proof of `le:injective_minima`, lines 1221--1225] A rank-`k`
   matrix in the row lattice contains `k` independent integral rows.  The
   row-space equality is the bridge from the matrix rank condition to the
   finite-dimensional independence argument. -/
theorem exists_linearIndependent_rows_of_rowMatrixRank_eq
    {m k n : ℕ} (V : Grassmannian K m k)
    (A : rowMatrixZLattice V n)
    (hA : rowMatrixRank V A = k) :
    ∃ e : Fin k → Fin n,
      LinearIndependent K (fun i =>
        ((rowMatrixZLatticeEquiv V A (e i) : rowZLattice V) :
          rowRealSpan V)) := by
  let B := (integralRowMatricesEquivRowMatrixZLattice V n).symm A
  have hspace : matrixRowSpace B.1 = V.1 :=
    (rowMatrixRank_eq_iff_rowSpace_eq V A).1 hA
  have hfin : Module.finrank K
      (Submodule.span K (Set.range (algebraicMatrix B.1).row)) = k := by
    have hfin' : Module.finrank K (matrixRowSpace B.1) = k := by
      rw [hspace, V.2]
    change Module.finrank K (matrixRowSpace B.1) = k
    exact hfin'
  obtain ⟨e, he⟩ :=
    exists_linearIndependent_subfamily_of_finrank_span_eq
      (algebraicMatrix B.1).row hfin
  let u : Fin k → V.1 := fun i =>
    ⟨fun j => ((B.1.row (e i) j : 𝓞 K) : K), B.2 (e i)⟩
  have hu : LinearIndependent K u := by
    apply LinearIndependent.of_comp V.1.subtype
    have hu' : (fun i => (u i : Fin m → K)) =
        (algebraicMatrix B.1).row ∘ e := by
      funext i j
      rfl
    change LinearIndependent K (fun i => (u i : Fin m → K))
    rw [hu']
    exact he
  have hrow (i : Fin k) :
      (((rowMatrixZLatticeEquiv V A (e i) : rowZLattice V) :
        rowRealSpan V) : RowVector K m) =
        rowSpaceVectorEmbeddingK V (u i) := by
    apply PiLp.ext
    intro j
    have hBA : integralRowMatricesEquivRowMatrixZLattice V n B = A :=
      (integralRowMatricesEquivRowMatrixZLattice V n).apply_symm_apply A
    have hcoe := rowMatrixZLatticeEquiv_coe V A (e i)
    have hArow := congrFun (congrArg (fun C : rowMatrixZLattice V n =>
        ((C : rowMatrixRealSpan V n) : M n m (K_ℝ[K])))
      (show integralRowMatricesEquivRowMatrixZLattice V n B = A from hBA)) (e i)
    have hArow' := congrFun hArow j
    have hBrow := congrArg (fun x : M n m (K_ℝ[K]) => x (e i) j)
      (integralRowMatricesEquivRowMatrixZLattice_coe V n B)
    have hcoe' := congrFun hcoe j
    simpa [u, rowSpaceVectorEmbeddingK, embedMatrix] using
      hcoe'.trans (hArow'.symm.trans hBrow.symm)
  refine ⟨e, ?_⟩
  apply LinearIndependent.of_comp (rowRealSpanSubtypeKLinearMap V)
  have hrow' : (rowRealSpanSubtypeKLinearMap V) ∘ (fun i =>
      (((rowMatrixZLatticeEquiv V A (e i) : rowZLattice V) :
        rowRealSpan V))) =
      rowSpaceVectorEmbeddingK V ∘ u := by
    funext i
    simpa [Function.comp_def, rowRealSpanSubtypeKLinearMap] using hrow i
  rw [hrow']
  exact hu.map' (rowSpaceVectorEmbeddingK V)
    (LinearMap.ker_eq_bot.mpr (rowSpaceVectorEmbeddingK_injective V))

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
