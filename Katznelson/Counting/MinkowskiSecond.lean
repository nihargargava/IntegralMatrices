import Katznelson.Counting.SuccessiveMinima
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# A Euclidean Minkowski-second-theorem supporting argument

Fieker--Stehlé, *Short Bases of Lattices over Number Fields*, Theorem 2
(`papers/Fieker-Stehle-ShortBases-2010.pdf`, p. 3), reduces its product bound
to the classical Minkowski second theorem for the underlying integral lattice.
This module supplies that standard Euclidean argument from the first
Minkowski theorem already proved in `GeometryOfNumbers.lean`.  It is supporting
infrastructure for the cited input, not a replacement proof of a manuscript
step or a change of the paper's norm convention.

The proof uses the usual diagonal rescaling in the Gram--Schmidt orthonormal
basis of the real successive minima.  The numerical constant is deliberately
non-sharp: only a dimension-dependent constant is used by the manuscript and
by Fieker--Stehlé's reduction.
-/

namespace Katznelson

open MeasureTheory Set Metric Module
open scoped Classical RealInnerProductSpace

section DiagonalRescaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/- [Lean infrastructure] The diagonal map in an orthonormal basis.  It is the
   linear-algebra realization of the rescaling used in the standard proof of
   the Euclidean Minkowski second theorem. -/
noncomputable def diagonalScaling {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ) : E →L[ℝ] E :=
  b.toBasis.constrL (fun i => a i • b i)

/- [Lean infrastructure] The diagonal rescaling has the prescribed action on
   the chosen orthonormal basis. -/
theorem diagonalScaling_apply_basis {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (i : Fin n) : diagonalScaling b a (b i) = a i • b i := by
  exact b.toBasis.constrL_basis _ i

/- [Lean infrastructure] The determinant of the diagonal rescaling is the
   product of its diagonal factors. -/
theorem diagonalScaling_det {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ) :
    LinearMap.det (diagonalScaling b a).toLinearMap = ∏ i, a i := by
  rw [← LinearMap.det_toMatrix b.toBasis]
  rw [show LinearMap.toMatrix b.toBasis b.toBasis
      (diagonalScaling b a).toLinearMap = Matrix.diagonal a by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change b.toBasis.repr (diagonalScaling b a (b j)) i = _
    rw [show diagonalScaling b a (b j) = a j • b j by
      exact b.toBasis.constrL_basis _ j]
    rw [map_smul]
    have hrepr : b.toBasis.repr (b j) = Finsupp.single j (1 : ℝ) :=
      b.toBasis.repr_self j
    rw [hrepr]
    by_cases h : i = j <;> simp [h]
  ]
  exact Matrix.det_diagonal

/- [Lean infrastructure] Coordinates of a diagonal rescaling are rescaled
   componentwise.  This is used below to identify the final nonzero
   Gram--Schmidt coordinate. -/
theorem diagonalScaling_repr_apply {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (z : E) (i : Fin n) :
    b.toBasis.repr (diagonalScaling b a z) i =
      a i * b.toBasis.repr z i := by
  change b.toBasis.repr ((diagonalScaling b a).toLinearMap z) i = _
  have hmatrix : LinearMap.toMatrix b.toBasis b.toBasis
      (diagonalScaling b a).toLinearMap = Matrix.diagonal a := by
    ext p q
    rw [LinearMap.toMatrix_apply]
    change b.toBasis.repr (diagonalScaling b a (b q)) p = _
    rw [show diagonalScaling b a (b q) = a q • b q by
      exact b.toBasis.constrL_basis _ q]
    rw [map_smul]
    have hrepr : b.toBasis.repr (b q) = Finsupp.single q (1 : ℝ) :=
      b.toBasis.repr_self q
    rw [hrepr]
    by_cases h : p = q <;> simp [h]
  have h := LinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis
    (diagonalScaling b a).toLinearMap z
  rw [hmatrix] at h
  have hi := congrFun h i
  simpa only [Matrix.mulVec_diagonal] using hi.symm

/- [Lean infrastructure] A diagonal rescaling with no zero factor is an
   invertible real-linear map. -/
theorem diagonalScaling_det_ne_zero {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) :
    LinearMap.det (diagonalScaling b a).toLinearMap ≠ 0 := by
  rw [diagonalScaling_det]
  exact Finset.prod_ne_zero_iff.mpr (by
    intro i _
    exact ha i)

/- [Lean infrastructure] Pulling a lattice back through the diagonal
   rescaling divides its covolume by the absolute diagonal determinant.  This
   is a direct use of the attributed covolume-change interface in
   `PaperMetric.lean`. -/
theorem covolume_comap_diagonalScaling {n : ℕ}
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) :
    ZLattice.covolume
        (ZLattice.comap ℝ L (diagonalScaling b a).toLinearMap) =
      |(∏ i, a i)⁻¹| * ZLattice.covolume L := by
  have hdet := diagonalScaling_det_ne_zero b a ha
  let e : E ≃L[ℝ] E :=
    (diagonalScaling b a).toContinuousLinearEquivOfDetNeZero hdet
  have he : e.toLinearMap = (diagonalScaling b a).toLinearMap := by
    dsimp [e]
    rfl
  have hcov := covolume_comap_symm_det L volume e.symm
  rw [show e.symm.symm.toLinearMap = (diagonalScaling b a).toLinearMap by
    simpa [he] using he] at hcov
  have hinvdet : LinearMap.det e.symm.toLinearMap =
      (LinearMap.det e.toLinearMap)⁻¹ := by
    change LinearMap.det ((e.toLinearEquiv).symm : E →ₗ[ℝ] E) =
      (LinearMap.det (e.toLinearEquiv : E →ₗ[ℝ] E))⁻¹
    exact LinearEquiv.det_coe_symm e.toLinearEquiv
  rw [hinvdet, he, diagonalScaling_det] at hcov
  exact hcov

/- [Lean infrastructure] If a vector has no Gram--Schmidt coordinates after
   `j`, diagonal rescaling by the reciprocal positive, nondecreasing factors
   has the elementary norm bound needed in the standard Minkowski-second
   argument.  The factor `n` comes only from the triangle inequality. -/
theorem diagonalScaling_norm_le_of_final_support {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (hapos : ∀ i, 0 < a i)
    (hmono : ∀ i j, i.val ≤ j.val → a i ≤ a j)
    (z y : E)
    (hy : y = diagonalScaling b (fun i => (a i)⁻¹) z)
    (j : Fin n)
    (hsupport : ∀ i, j.val < i.val → b.toBasis.repr y i = 0) :
    ‖z‖ ≤ (n : ℝ) * a j * ‖y‖ := by
  have hcoord_y (i : Fin n) : |b.toBasis.repr y i| ≤ ‖y‖ := by
    rw [b.coe_toBasis_repr_apply, b.repr_apply_apply]
    simpa using (abs_real_inner_le_norm (b i) y)
  have hscale (i : Fin n) : b.toBasis.repr y i =
      (a i)⁻¹ * b.toBasis.repr z i := by
    rw [hy]
    exact diagonalScaling_repr_apply b (fun i => (a i)⁻¹) z i
  have hcoord_z (i : Fin n) : b.toBasis.repr z i =
      a i * b.toBasis.repr y i := by
    rw [hscale]
    field_simp [ne_of_gt (hapos i)]
  have hbound (i : Fin n) : |b.toBasis.repr z i| ≤ a j * ‖y‖ := by
    by_cases hij : i.val ≤ j.val
    · rw [hcoord_z, abs_mul, abs_of_pos (hapos i)]
      calc
        a i * |b.toBasis.repr y i| ≤ a i * ‖y‖ :=
          mul_le_mul_of_nonneg_left (hcoord_y i) (le_of_lt (hapos i))
        _ ≤ a j * ‖y‖ :=
          mul_le_mul_of_nonneg_right (hmono i j hij) (norm_nonneg _)
    · have hji : j.val < i.val := Nat.lt_of_not_ge hij
      have hyzero : b.toBasis.repr y i = 0 := hsupport i hji
      have hzzero : b.toBasis.repr z i = 0 := by
        have hcoordzi := hcoord_z i
        rw [hyzero] at hcoordzi
        simpa using hcoordzi
      rw [hzzero, abs_zero]
      exact mul_nonneg (le_of_lt (hapos j)) (norm_nonneg _)
  calc
    ‖z‖ = ‖∑ i, b.toBasis.repr z i • b.toBasis i‖ := by
      rw [b.toBasis.sum_repr]
    _ ≤ ∑ i, ‖b.toBasis.repr z i • b.toBasis i‖ := norm_sum_le _ _
    _ = ∑ i, |b.toBasis.repr z i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul]
      change ‖b.toBasis.repr z i‖ * ‖b i‖ = _
      rw [b.norm_eq_one, mul_one, Real.norm_eq_abs]
    _ ≤ ∑ _ : Fin n, a j * ‖y‖ := by
      exact Finset.sum_le_sum (fun i _ => hbound i)
    _ = (n : ℝ) * a j * ‖y‖ := by
      simp [mul_assoc]

/- [Lean infrastructure] A nonzero vector has a final nonzero coordinate in
   a finite ordered orthonormal basis.  This finite-support observation is
   the index choice in the standard diagonal-rescaling proof. -/
theorem exists_final_nonzero_coordinate {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (y : E) (hy : y ≠ 0) :
    ∃ j : Fin n, b.toBasis.repr y j ≠ 0 ∧
      ∀ i, j.val < i.val → b.toBasis.repr y i = 0 := by
  have hrepr : b.toBasis.repr y ≠ 0 := by
    intro hzero
    apply hy
    apply b.toBasis.repr.injective
    simpa using hzero
  let s : Finset (Fin n) := (b.toBasis.repr y).support
  have hs : s.Nonempty := Finsupp.support_nonempty_iff.mpr hrepr
  let j : Fin n := s.max' hs
  refine ⟨j, ?_, ?_⟩
  · exact Finsupp.mem_support_iff.mp (Finset.max'_mem s hs)
  · intro i hji
    by_contra hi
    have his : i ∈ s := Finsupp.mem_support_iff.mpr hi
    have hij : i ≤ j := Finset.le_max' s i his
    omega

/- [Lean infrastructure] In the Gram--Schmidt basis of an ordered family,
   every vector spanned by the entries strictly before `j` has vanishing
   `j`-coordinate.  This is the triangularity bridge between the coordinate
   argument and the manuscript's preceding-vector span. -/
theorem gramSchmidt_coordinate_zero_of_mem_previous_span {n : ℕ}
    (hn : Module.finrank ℝ E = n) (x : Fin n → E)
    (j : Fin n) {z : E}
    (hz : z ∈ Submodule.span ℝ
      (Set.range (fun i : Fin j.val =>
        x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩))) :
    (InnerProductSpace.gramSchmidtOrthonormalBasis (𝕜 := ℝ) (E := E)
      (ι := Fin n) (by simpa using hn) x).toBasis.repr z j = 0 := by
  let b : OrthonormalBasis (Fin n) ℝ E :=
    InnerProductSpace.gramSchmidtOrthonormalBasis (𝕜 := ℝ) (E := E)
      (ι := Fin n) (by simpa using hn) x
  change b.toBasis.repr z j = 0
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · rintro w ⟨i, rfl⟩
    let i' : Fin n := ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩
    change b.toBasis.repr (x i') j = 0
    rw [b.coe_toBasis_repr_apply]
    exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular'
      (𝕜 := ℝ) (E := E) (ι := Fin n) (by simpa using hn) x
      (show i' < j by
        change i.val < j.val
        exact i.isLt)
  · simp
  · intro u v _ _ hpu hpv
    rw [map_add]
    change b.toBasis.repr u j + b.toBasis.repr v j = 0
    rw [hpu, hpv, add_zero]
  · intro c u _ hpu
    rw [map_smul]
    change c * b.toBasis.repr u j = 0
    rw [hpu, mul_zero]

/- [Lean infrastructure] The two diagonal maps with reciprocal positive
   factors are inverse on the ambient Euclidean space. -/
theorem diagonalScaling_reciprocal_apply {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (hapos : ∀ i, 0 < a i) (y : E) :
    diagonalScaling b (fun i => (a i)⁻¹)
      (diagonalScaling b a y) = y := by
  apply b.toBasis.ext_elem
  intro i
  rw [diagonalScaling_repr_apply, diagonalScaling_repr_apply]
  field_simp [ne_of_gt (hapos i)]

/- [Lean infrastructure] The elementary real-power estimate that turns a
   strict product-bound failure into a short vector after diagonal scaling.
   It isolates all `rpow` normalization from the geometric argument. -/
theorem minkowski_radius_lt_inv_of_product_lt
    (n : ℕ) (hn : 0 < n) (C D P : ℝ)
    (hC : 0 < C) (hD : 0 < D) (hP : 0 < P)
    (hproduct : ((n : ℝ) * C) ^ n * D < P) :
    C * (D / P) ^ (1 / (n : ℝ)) < 1 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let a : ℝ := (n : ℝ) * C
  have ha : 0 < a := by
    dsimp [a]
    exact mul_pos hnR hC
  have hroot : (D / P) ^ ((n : ℝ)⁻¹) < a⁻¹ := by
    apply (Real.rpow_inv_lt_iff_of_pos
      (div_nonneg hD.le hP.le) (inv_nonneg.mpr ha.le) hnR).2
    rw [Real.rpow_natCast, inv_pow]
    apply (div_lt_iff₀ hP).2
    calc
      D = (a ^ n)⁻¹ * (a ^ n * D) := by
        field_simp [ne_of_gt ha]
      _ < (a ^ n)⁻¹ * P :=
        mul_lt_mul_of_pos_left hproduct (inv_pos.mpr (pow_pos ha _))
  rw [show 1 / (n : ℝ) = (n : ℝ)⁻¹ by ring]
  calc
    C * (D / P) ^ (n : ℝ)⁻¹ < C * a⁻¹ :=
      mul_lt_mul_of_pos_left hroot hC
    _ = (n : ℝ)⁻¹ := by
      dsimp [a]
      field_simp [ne_of_gt hnR, ne_of_gt hC]

end DiagonalRescaling

section EuclideanSecond

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/- [derived consequence] This is the standard diagonal-rescaling proof of a
   deliberately non-sharp Euclidean Minkowski-II product estimate, derived
   from `exists_nonzero_latticeVector_norm_le_covolume_rpow`.  It supplies the
   geometric core used below for the cited Fieker--Stehlé Theorem 2; it is not
   presented as a replacement for a manuscript step. -/
theorem euclidean_product_norm_le_covolume_of_ordered_minima
    {n : ℕ} (hn : Module.finrank ℝ E = n) (hnpos : 0 < n)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (x : Fin n → L)
    (hxne : ∀ i, x i ≠ 0)
    (hmono : ∀ i j, i.val ≤ j.val →
      ‖((x i : L) : E)‖ ≤ ‖((x j : L) : E)‖)
    (hmin : ∀ (j : Fin n) (z : L),
      (z : E) ∉ Submodule.span ℝ
        (Set.range (fun i : Fin j.val =>
          ((x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩ : L) : E))) →
      ‖((x j : L) : E)‖ ≤ ‖(z : E)‖) :
    (∏ i, ‖((x i : L) : E)‖) ≤
      ((n : ℝ) * minkowskiConstant (E := E)) ^ n *
        ZLattice.covolume L := by
  let xE : Fin n → E := fun i => (x i : E)
  let a : Fin n → ℝ := fun i => ‖xE i‖
  let P : ℝ := ∏ i, a i
  let D : ℝ := ZLattice.covolume L
  have hapos (i : Fin n) : 0 < a i := by
    dsimp [a, xE]
    apply norm_pos_iff.mpr
    intro hzero
    apply hxne i
    exact Subtype.ext hzero
  have hPpos : 0 < P := by
    apply Finset.prod_pos
    intro i _
    exact hapos i
  have hDpos : 0 < D := by
    exact ZLattice.covolume_pos L
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hnpos
  have hCpos : 0 < minkowskiConstant (E := E) :=
    minkowskiConstant_pos (E := E)
  let b : OrthonormalBasis (Fin n) ℝ E :=
    InnerProductSpace.gramSchmidtOrthonormalBasis (𝕜 := ℝ) (E := E)
      (ι := Fin n) (by simpa using hn) xE
  let S : E →L[ℝ] E := diagonalScaling b a
  have hSdet : LinearMap.det S.toLinearMap ≠ 0 := by
    dsimp [S]
    apply diagonalScaling_det_ne_zero
    intro i
    exact ne_of_gt (hapos i)
  let e : E ≃L[ℝ] E := S.toContinuousLinearEquivOfDetNeZero hSdet
  have he : e.toLinearMap = S.toLinearMap := by
    dsimp [e]
    rfl
  let M : Submodule ℤ E := ZLattice.comap ℝ L e.toLinearMap
  have hMeq : M = ZLattice.comap ℝ L S.toLinearMap := by
    simp only [M, he]
  have hcov : ZLattice.covolume M = D / P := by
    rw [hMeq]
    change ZLattice.covolume (ZLattice.comap ℝ L
      (diagonalScaling b a).toLinearMap) = _
    rw [covolume_comap_diagonalScaling L b a
      (fun i => ne_of_gt (hapos i))]
    change |P⁻¹| * D = D / P
    rw [abs_of_pos (inv_pos.mpr hPpos)]
    field_simp [ne_of_gt hPpos]
  change P ≤ ((n : ℝ) * minkowskiConstant (E := E)) ^ n * D
  by_contra hnot
  have hproduct : ((n : ℝ) * minkowskiConstant (E := E)) ^ n * D < P :=
    lt_of_not_ge hnot
  obtain ⟨y, hyne, hybound⟩ :=
    exists_nonzero_latticeVector_norm_le_covolume_rpow M
  have hybound' : ‖(y : E)‖ ≤ minkowskiConstant (E := E) *
      (D / P) ^ (1 / (n : ℝ)) := by
    simpa only [hcov, hn] using hybound
  have hrad : minkowskiConstant (E := E) *
      (D / P) ^ (1 / (n : ℝ)) < 1 / (n : ℝ) :=
    minkowski_radius_lt_inv_of_product_lt n hnpos
      (minkowskiConstant (E := E)) D P hCpos hDpos hPpos hproduct
  have hynorm : ‖(y : E)‖ < 1 / (n : ℝ) := hybound'.trans_lt hrad
  have hyL : e.toLinearMap (y : E) ∈ L := by
    exact y.property
  have hzmem : S (y : E) ∈ L := by
    change S.toLinearMap (y : E) ∈ L
    simpa only [he] using hyL
  let z : L := ⟨S (y : E), hzmem⟩
  have hyrel : (y : E) = diagonalScaling b (fun i => (a i)⁻¹)
      (z : E) := by
    change (y : E) = diagonalScaling b (fun i => (a i)⁻¹)
      (diagonalScaling b a (y : E))
    exact (diagonalScaling_reciprocal_apply b a hapos (y : E)).symm
  obtain ⟨j, hjne, hsupport⟩ :=
    exists_final_nonzero_coordinate b (y : E) (by
      intro hyzero
      apply hyne
      exact Subtype.ext hyzero)
  have hzcoord : b.toBasis.repr (z : E) j ≠ 0 := by
    intro hzero
    apply hjne
    rw [hyrel, diagonalScaling_repr_apply, hzero, mul_zero]
  have hzprev : (z : E) ∉ Submodule.span ℝ
      (Set.range (fun i : Fin j.val =>
        ((x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩ : L) : E))) := by
    intro hzspan
    apply hzcoord
    exact gramSchmidt_coordinate_zero_of_mem_previous_span hn xE j hzspan
  have hminz : a j ≤ ‖(z : E)‖ := by
    simpa only [a, xE] using hmin j z hzprev
  have hznorm : ‖(z : E)‖ ≤ (n : ℝ) * a j * ‖(y : E)‖ :=
    diagonalScaling_norm_le_of_final_support b a hapos
      (fun i j hij => hmono i j hij) (z : E) (y : E) hyrel j hsupport
  have hsmall : (n : ℝ) * ‖(y : E)‖ < 1 := by
    calc
      (n : ℝ) * ‖(y : E)‖ = ‖(y : E)‖ * (n : ℝ) := mul_comm _ _
      _ < 1 := (lt_div_iff₀ hnR).mp hynorm
  have hstrict : (n : ℝ) * a j * ‖(y : E)‖ < a j := by
    calc
      (n : ℝ) * a j * ‖(y : E)‖ = a j * ((n : ℝ) * ‖(y : E)‖) := by ring
      _ < a j * 1 := mul_lt_mul_of_pos_left hsmall (hapos j)
      _ = a j := mul_one _
  exact (lt_irrefl _ (hminz.trans_lt (hznorm.trans_lt hstrict)))

/- [derived consequence] Applying the preceding Euclidean product estimate
   to the paper's recursive construction `de:defi_of_successive`, lines
   871--879, with scalar field `ℝ`.  This is the real-lattice component of
   the cited Fieker--Stehlé input, not a new formulation of the manuscript's
   number-field minima. -/
theorem euclidean_successiveMinimum_product_le_covolume
    [LinearOrder E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    (∏ i : Fin (Module.finrank ℝ E),
      ‖((successiveMinimum ℝ L i : L) : E)‖) ≤
      ((Module.finrank ℝ E : ℝ) * minkowskiConstant (E := E)) ^
        Module.finrank ℝ E * ZLattice.covolume L := by
  let n : ℕ := Module.finrank ℝ E
  have hn : Module.finrank ℝ E = n := rfl
  have hnpos : 0 < n := by
    dsimp [n]
    exact Module.finrank_pos (R := ℝ) (M := E)
  have hfull : Module.finrank ℝ (Submodule.span ℝ (L : Set E)) = n := by
    rw [IsZLattice.span_top]
    simp [n]
  let x : Fin n → L := fun i => successiveMinimum ℝ L i
  apply euclidean_product_norm_le_covolume_of_ordered_minima
    hn hnpos L x
  · intro i
    exact successiveMinimum_ne_zero_of_finrank n L hfull i
  · intro i j hij
    exact successiveMinimum_norm_le_of_index_le_of_finrank
      n L hfull i j hij
  · intro j z hz
    have hspan : Submodule.span ℝ
        (Set.range (fun i : Fin j.val =>
          ((x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩ : L) : E))) =
        previousKSpan ℝ L j.val
          (successiveMinimaAux ℝ L j.val) := by
      unfold previousKSpan
      congr 1
      ext w
      constructor
      · rintro ⟨i, rfl⟩
        refine ⟨i, ?_⟩
        have haux := successiveMinimum_eq_successiveMinimaAux
          (S := ℝ) L i
        simpa [x, successiveMinimum] using
          congrArg (fun q : L => (q : E)) haux.symm
      · rintro ⟨i, rfl⟩
        refine ⟨i, ?_⟩
        have haux := successiveMinimum_eq_successiveMinimaAux
          (S := ℝ) L i
        simpa [x, successiveMinimum] using
          congrArg (fun q : L => (q : E)) haux
    have hzout : (z : E) ∉ previousKSpan ℝ L j.val
        (successiveMinimaAux ℝ L j.val) := by
      rw [← hspan]
      exact hz
    exact successiveMinimum_norm_min_of_nonempty L j
      (successiveMinimumSet_nonempty_of_finrank_at n L hfull j)
      z hzout

end EuclideanSecond

end Katznelson
