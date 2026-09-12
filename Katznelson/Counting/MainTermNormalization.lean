/-
Copyright (c) 2026 Nihar Gargava.
Released under GPL-3.0-only as described in the file LICENSE.
Authors: Nihar Gargava
-/

import Katznelson.MainTheorems
import Katznelson.Counting.Echelon
import Katznelson.Counting.PaperMetricRowSpaces
import Katznelson.Counting.UniformIntegral

/-!
# Exact normalization of the echelon main term

This file supplies the missing manuscript-facing bridge between the
echelon-coordinate expression in `papers/katznelson.tex`, equation
`eq:value_of_c`, lines 197--202, and the Grassmannian definition
`Katznelson.mainConstant`.  The measure calculation formalizes precisely the
change of variables and lattice normalization asserted in
`eq:summable_matrices` and `eq:d_D_defined`, lines 837--858.

## Provenance

* **paper:** `papers/katznelson.tex`, lines 192--202 and 837--858.
* **proof provenance (not a logical input):** Gargava--Serban--Viazovska,
  *Moments of the number of points in a bounded set for number field
  lattices*, Lemma 11 and Appendix A, checked-in as
  `papers/Gargava-Serban-Viazovska-Moments-2024.pdf`.  The normalization and
  denominator calculation motivate the organization below, but every theorem
  in this file is proved from prior Lean declarations and Mathlib; no result
  from that paper is assumed.
* **derived consequence:** the denominator index is the already-proved
  `echelonDenominatorMatrixModule_index`; echelon/Grassmannian reindexing is
  `tsum_echelon_reindex_rowSpaces`; independence of the auxiliary Haar
  realization is
  `rowMatrixNormalizedIntegralWithMeasure_eq_mainSummand`.
* **Lean infrastructure:** the maps and measures below merely package the
  literal coordinate map `x ↦ xD` and its push-forward measure.  No alternate
  summation argument or replacement main-term constant is introduced.
-/

namespace Katznelson

open MeasureTheory Set Module
open scoped BigOperators Classical MeasureTheory NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/- [Lean infrastructure] Use the same induced measurable and Borel
structures as `rowMatrixEuclideanMeasure` and
`PaperMetricRowSpaces.lean`.  Naming them locally is elaboration
bookkeeping only; both are the canonical structures inherited from the
ambient Frobenius-normed matrix space. -/
noncomputable local instance mainTermRowMatrixMeasurableSpace
    {m k n : ℕ} (V : Grassmannian K m k) :
    MeasurableSpace (rowMatrixRealSpan V n) :=
  @Subtype.instMeasurableSpace (M n m (K_ℝ[K]))
    (fun A => A ∈ rowMatrixRealSpan V n)
    (kRealMatrixMeasurableSpace (K := K))

local instance mainTermRowMatrixBorelSpace
    {m k n : ℕ} (V : Grassmannian K m k) :
    BorelSpace (rowMatrixRealSpan V n) :=
  @Subtype.borelSpace (M n m (K_ℝ[K])) inferInstance
    (kRealMatrixMeasurableSpace (K := K))
    (kRealMatrixBorelSpace (K := K))
    (fun A => A ∈ rowMatrixRealSpan V n)

noncomputable local instance mainTermMatrixMeasurableSpace
    {n m : ℕ} : MeasurableSpace (M n m (K_ℝ[K])) :=
  kRealMatrixMeasurableSpace (K := K)

local instance mainTermMatrixBorelSpace
    {n m : ℕ} : BorelSpace (M n m (K_ℝ[K])) :=
  kRealMatrixBorelSpace (K := K)

/- [Lean infrastructure] The globally fixed Frobenius norm is the iterated
`PiLp 2` norm.  Expose its canonical product inner product locally so that
Mathlib's relative-covolume theorem applies to the coefficient matrix
space without changing its norm or topology. -/
noncomputable local instance mainTermMatrixInnerProductSpace
    {n m : ℕ} : InnerProductSpace ℝ (M n m (K_ℝ[K])) := by
  let e : M n m (K_ℝ[K]) →ₗ[ℝ]
      PiLp 2 (fun _ : Fin n => PiLp 2 (fun _ : Fin m => K_ℝ[K])) :=
    { toFun := fun x => WithLp.toLp 2 (fun i => WithLp.toLp 2 (x i))
      map_add' := by
        intro x y
        ext i j
        rfl
      map_smul' := by
        intro c x
        ext i j
        rfl }
  refine
    { inner := fun x y => inner ℝ (e x) (e y)
      norm_sq_eq_re_inner := ?_
      conj_inner_symm := ?_
      add_left := ?_
      smul_left := ?_ }
  · intro x
    change ‖x‖ ^ 2 = RCLike.re (inner ℝ (e x) (e x))
    rw [← norm_sq_eq_re_inner]
    rfl
  · intro x y
    exact inner_conj_symm (e x) (e y)
  · intro x y z
    simpa only [map_add] using inner_add_left (e x) (e y) (e z)
  · intro x y c
    simpa only [map_smul] using inner_smul_left (e x) (e y) c

/- [Lean infrastructure, paper lines 837--854] The literal matrix product
`xD`, with the entries of `D` embedded in `K_ℝ`. -/
def echelonCoordinateProduct {n k m : ℕ} (D : EchelonMatrix K k m)
    (x : M n k (K_ℝ[K])) : M n m (K_ℝ[K]) :=
  fun i j => ∑ q : Fin k, x i q * numberEmbedding K ((D.1 : M k m K) q j)

@[simp]
theorem echelonCoordinateProduct_apply {n k m : ℕ}
    (D : EchelonMatrix K k m) (x : M n k (K_ℝ[K]))
    (i : Fin n) (j : Fin m) :
    echelonCoordinateProduct D x i j =
      ∑ q : Fin k, x i q * numberEmbedding K ((D.1 : M k m K) q j) := rfl

/- [Lean infrastructure, paper lines 837--854] Real linearity of `x ↦ xD`.
This is the scalar extension of `echelonRowCombinationLinearMap`; the formula
is kept literal because it is the integrand in `eq:value_of_c`. -/
def echelonCoordinateLinearMap {n k m : ℕ} (D : EchelonMatrix K k m) :
    M n k (K_ℝ[K]) →ₗ[ℝ] M n m (K_ℝ[K]) where
  toFun := echelonCoordinateProduct D
  map_add' x y := by
    ext i j
    change (∑ q : Fin k,
        (x i q + y i q) * numberEmbedding K ((D.1 : M k m K) q j)) =
      (∑ q : Fin k, x i q * numberEmbedding K ((D.1 : M k m K) q j)) +
      ∑ q : Fin k, y i q * numberEmbedding K ((D.1 : M k m K) q j)
    simp only [add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    ext i j
    change (∑ q : Fin k,
        (r • x i q) * numberEmbedding K ((D.1 : M k m K) q j)) =
      r • ∑ q : Fin k,
        x i q * numberEmbedding K ((D.1 : M k m K) q j)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    change (r • x i q) * numberEmbedding K ((D.1 : M k m K) q j) =
      r • (x i q * numberEmbedding K ((D.1 : M k m K) q j))
    exact kReal_smul_assoc_real K r (x i q)
      (numberEmbedding K ((D.1 : M k m K) q j))

@[simp]
theorem echelonCoordinateLinearMap_apply {n k m : ℕ}
    (D : EchelonMatrix K k m) (x : M n k (K_ℝ[K])) :
    echelonCoordinateLinearMap D x = echelonCoordinateProduct D x := rfl

/- [derived consequence, paper lines 844--848] Full row rank of a reduced
echelon matrix makes the literal coordinate map injective over `K_ℝ`.  The
proof reads coefficients in the pivot columns, so it does not use a field
structure on the product algebra `K_ℝ`. -/
theorem echelonCoordinateLinearMap_injective {n k m : ℕ}
    (D : EchelonMatrix K k m) :
    Function.Injective (echelonCoordinateLinearMap (n := n) D) := by
  intro x y hxy
  ext i q
  have hp := congrFun (congrFun hxy i) (echelonLeadingColumn D q)
  simp only [echelonCoordinateLinearMap_apply, echelonCoordinateProduct_apply]
    at hp
  have hsum (z : M n k (K_ℝ[K])) :
      (∑ q' : Fin k, z i q' * numberEmbedding K
        ((D.1 : M k m K) q' (echelonLeadingColumn D q))) = z i q := by
    rw [Finset.sum_eq_single q]
    · rw [echelon_pivotColumn_apply]
      rw [if_pos rfl]
      change z i q * numberEmbeddingRingHom K 1 = z i q
      rw [map_one, mul_one]
    · intro q' hq' hne
      rw [echelon_pivotColumn_apply]
      simp [hne, numberEmbedding_zero]
    · simp
  rw [hsum x, hsum y] at hp
  exact hp

/- [derived consequence, paper lines 844--854] The image of `x ↦ xD` lies
in the real row-matrix space attached to the rational row space of `D`. -/
theorem echelonCoordinateProduct_mem_rowMatrixRealSpan {n k m : ℕ}
    (D : EchelonMatrix K k m) (x : M n k (K_ℝ[K])) :
    echelonCoordinateProduct D x ∈
      rowMatrixRealSpan (echelonRowSpace D) n := by
  rw [rowMatrixRealSpan_eq_rowwise]
  intro i
  change rowVectorOfFun (echelonCoordinateProduct D x i) ∈
    rowRealSpan (echelonRowSpace D)
  have hrow (q : Fin k) :
      rowVectorOfFun (fun j : Fin m =>
        numberEmbedding K ((D.1 : M k m K) q j)) ∈
        rowRealSpan (echelonRowSpace D) := by
    let v : (echelonRowSpace D).1 :=
      ⟨D.1.row q, Submodule.subset_span ⟨q, rfl⟩⟩
    have hv : v ∈ Submodule.span ℚ
        (Set.range (fun w : integralRowModule (echelonRowSpace D) =>
          (integralRowToRowSpace (echelonRowSpace D) w :
            (echelonRowSpace D).1))) := by
      rw [span_range_integralRowToRowSpace_rat]
      trivial
    change rowSpaceVectorEmbeddingQ (echelonRowSpace D) v ∈
      rowRealSpan (echelonRowSpace D)
    exact rowSpaceVectorEmbeddingQ_mem_rowRealSpan_of_mem_ratSpan
      (echelonRowSpace D) v hv
  have hsum : (∑ q : Fin k,
      x i q • rowVectorOfFun (fun j : Fin m =>
        numberEmbedding K ((D.1 : M k m K) q j))) ∈
      rowRealSpan (echelonRowSpace D) := by
    exact (rowRealSpan (echelonRowSpace D)).sum_mem
      (fun q hq => kReal_smul_mem_rowRealSpan
        (echelonRowSpace D) (x i q) (hrow q))
  convert hsum using 1
  apply PiLp.ext
  intro j
  simp [echelonCoordinateProduct, smul_eq_mul]

/- [Lean infrastructure, paper lines 844--854] The coordinate map with its
codomain restricted to the manuscript's subspace `M_{n×k}(K_ℝ)·D`. -/
def echelonCoordinateToRowSpan {n k m : ℕ} (D : EchelonMatrix K k m) :
    M n k (K_ℝ[K]) →ₗ[ℝ]
      rowMatrixRealSpan (echelonRowSpace D) n :=
  (echelonCoordinateLinearMap D).codRestrict
    (rowMatrixRealSpan (echelonRowSpace D) n)
    (echelonCoordinateProduct_mem_rowMatrixRealSpan D)

theorem echelonCoordinateToRowSpan_injective {n k m : ℕ}
    (D : EchelonMatrix K k m) :
    Function.Injective (echelonCoordinateToRowSpan (n := n) D) := by
  intro x y hxy
  apply echelonCoordinateLinearMap_injective D
  exact congrArg Subtype.val hxy

/- [derived consequence, paper lines 844--854] The literal coordinate map is
onto the full real subspace `M_{n×k}(K_ℝ)·D`. -/
theorem echelonCoordinateToRowSpan_surjective {n k m : ℕ}
    (D : EchelonMatrix K k m) :
    Function.Surjective (echelonCoordinateToRowSpan (n := n) D) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := echelonCoordinateToRowSpan (n := n) D) ?_).mp
    (echelonCoordinateToRowSpan_injective D)
  rw [rowMatrixRealSpan_finrank]
  change Module.finrank ℝ (Fin n → Fin k → K_ℝ[K]) =
    n * (k * degree K)
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp [NumberField.mixedEmbedding.euclidean.finrank, degree,
    mul_assoc, mul_left_comm, mul_comm]

/- [Lean infrastructure, paper lines 844--854] The exact real-linear
equivalence represented by `x ↦ xD`. -/
def echelonCoordinateEquiv {n k m : ℕ} (D : EchelonMatrix K k m) :
    M n k (K_ℝ[K]) ≃ₗ[ℝ]
      rowMatrixRealSpan (echelonRowSpace D) n :=
  LinearEquiv.ofBijective (echelonCoordinateToRowSpan D)
    ⟨echelonCoordinateToRowSpan_injective D,
      echelonCoordinateToRowSpan_surjective D⟩

@[simp]
theorem echelonCoordinateEquiv_apply_coe {n k m : ℕ}
    (D : EchelonMatrix K k m) (x : M n k (K_ℝ[K])) :
    ((echelonCoordinateEquiv D x :
        rowMatrixRealSpan (echelonRowSpace D) n) :
      M n m (K_ℝ[K])) = echelonCoordinateProduct D x := rfl

/- [Lean infrastructure] In finite dimension the preceding algebraic
equivalence is automatically continuous. -/
def echelonCoordinateContinuousEquiv {n k m : ℕ}
    (D : EchelonMatrix K k m) :
    M n k (K_ℝ[K]) ≃L[ℝ]
      rowMatrixRealSpan (echelonRowSpace D) n :=
  (echelonCoordinateEquiv D).toContinuousLinearEquiv

/- [Lean infrastructure, paper equation `eq:d_D_defined`, lines 847--853]
The measure on the image of `x ↦ xD` obtained by transporting the literal
coordinate measure.  This is the measure-theoretic realization of the
Jacobian in manuscript line 844; defining it as a push-forward keeps the
normalization exact. -/
noncomputable def echelonPushforwardMeasure {n k m : ℕ}
    (D : EchelonMatrix K k m) (mu : Measure (M n k (K_ℝ[K]))) :
    Measure (rowMatrixRealSpan (echelonRowSpace D) n) :=
  mu.map (echelonCoordinateContinuousEquiv D)

/- [derived consequence, paper equation `eq:d_D_defined`, lines 847--853]
Transport by the coordinate equivalence preserves the additive-Haar
property.  This is Mathlib's standard push-forward theorem for continuous
linear equivalences, not an additional mathematical input. -/
theorem echelonPushforwardMeasure_isAddHaarMeasure {n k m : ℕ}
    (D : EchelonMatrix K k m) (mu : Measure (M n k (K_ℝ[K])))
    [Measure.IsAddHaarMeasure mu] :
    Measure.IsAddHaarMeasure (echelonPushforwardMeasure D mu) := by
  unfold echelonPushforwardMeasure
  exact (echelonCoordinateContinuousEquiv D).isAddHaarMeasure_map mu

/- [derived consequence, paper equation `eq:d_D_defined`, lines 847--853]
Exact change of variables for the literal integrand `f (xD)`.  Since the
target measure is defined by push-forward, no determinant, norm-equivalence
constant, or integrability hypothesis is needed for this identity. -/
theorem integral_echelonPushforwardMeasure {n k m : ℕ}
    (D : EchelonMatrix K k m) (mu : Measure (M n k (K_ℝ[K])))
    (f : M n m (K_ℝ[K]) → ℝ) :
    (∫ A : rowMatrixRealSpan (echelonRowSpace D) n,
        f (A : M n m (K_ℝ[K])) ∂(echelonPushforwardMeasure D mu)) =
      ∫ x : M n k (K_ℝ[K]), f (echelonCoordinateProduct D x) ∂mu := by
  unfold echelonPushforwardMeasure
  change
    (∫ A : rowMatrixRealSpan (echelonRowSpace D) n,
        f (A : M n m (K_ℝ[K]))
          ∂mu.map (echelonCoordinateContinuousEquiv D).toHomeomorph) =
      ∫ x : M n k (K_ℝ[K]),
        f ((((echelonCoordinateContinuousEquiv D) x :
          rowMatrixRealSpan (echelonRowSpace D) n) :
            M n m (K_ℝ[K]))) ∂mu
  exact
    (echelonCoordinateContinuousEquiv D).toHomeomorph.isClosedEmbedding.integral_map
      (μ := mu) (fun A : rowMatrixRealSpan (echelonRowSpace D) n =>
        f (A : M n m (K_ℝ[K])))

/- [Lean infrastructure, paper equations `de:denonimator` and
`eq:d_D_defined`, lines 192--195 and 844--853] The literal coefficient
lattice
`{x : M_{n×k}(K_ℝ) | xD ∈ M_{n×m}(O_K)}`.  It is defined as the pullback of
`M_n(Λ_D)` under the proved coordinate equivalence, so its carrier retains
the manuscript's condition exactly. -/
noncomputable def echelonCoefficientZLattice {n k m : ℕ}
    (D : EchelonMatrix K k m) : Submodule ℤ (M n k (K_ℝ[K])) :=
  ZLattice.comap ℝ (rowMatrixZLattice (echelonRowSpace D) n)
    (echelonCoordinateContinuousEquiv D).toLinearMap

@[simp]
theorem mem_echelonCoefficientZLattice_iff {n k m : ℕ}
    (D : EchelonMatrix K k m) (x : M n k (K_ℝ[K])) :
    x ∈ echelonCoefficientZLattice D ↔
      echelonCoordinateToRowSpan D x ∈
        rowMatrixZLattice (echelonRowSpace D) n := by
  rfl

/- [derived consequence, paper definition `de:denonimator`, lines 192--195]
The pullback lattice is exactly the mixed-embedding image of the manuscript's
rowwise denominator module.  Thus the analytic pullback above and the
arithmetic module whose index is computed by
`echelonDenominatorMatrixModule_index` are not merely isomorphic: they have
the same points in the coordinate space. -/
theorem mem_echelonCoefficientZLattice_iff_exists_denominatorMatrix
    {n k m : ℕ} (D : EchelonMatrix K k m) (x : M n k (K_ℝ[K])) :
    x ∈ echelonCoefficientZLattice D ↔
      ∃ C : Fin n → Fin k → 𝓞 K,
        C ∈ echelonDenominatorMatrixModule D ∧ embedMatrix C = x := by
  constructor
  · intro hx
    change echelonCoordinateProduct D x ∈
      embeddedRowMatrixModule (echelonRowSpace D) n at hx
    obtain ⟨B, hB, hBx⟩ :=
      (mem_embeddedRowMatrixModule_iff (echelonRowSpace D)
        (echelonCoordinateProduct D x)).1 hx
    choose c hc using fun i =>
      (mem_echelonLambda_iff_exists_denominator_coeff D (B.row i)).1 (hB i)
    let C : Fin n → Fin k → 𝓞 K := fun i q => (c i).1 q
    have hC : C ∈ echelonDenominatorMatrixModule D := fun i => (c i).2
    refine ⟨C, hC, ?_⟩
    ext i q
    let p : Fin m := echelonLeadingColumn D q
    have hp := congrFun (congrFun hBx i) p
    have hsum (z : M n k (K_ℝ[K])) :
        (∑ q' : Fin k, z i q' * numberEmbedding K
          ((D.1 : M k m K) q' p)) = z i q := by
      rw [Finset.sum_eq_single q]
      · rw [echelon_pivotColumn_apply]
        rw [if_pos rfl]
        change z i q * numberEmbeddingRingHom K 1 = z i q
        rw [map_one, mul_one]
      · intro q' hq' hne
        rw [echelon_pivotColumn_apply]
        simp [hne, numberEmbedding_zero]
      · simp
    change numberEmbedding K (B i p : K) =
      (∑ q' : Fin k, x i q' * numberEmbedding K
        ((D.1 : M k m K) q' p)) at hp
    rw [hsum x] at hp
    have hcq : (B i p : K) = (C i q : K) := by
      have h := hc i p
      dsimp [C]
      rw [Finset.sum_eq_single q] at h
      · dsimp [p] at h
        rw [echelon_pivotColumn_apply] at h
        simpa using h
      · intro q' hq' hne
        rw [echelon_pivotColumn_apply]
        simp [hne]
      · simp
    change numberEmbedding K (C i q : K) = x i q
    rw [← hcq]
    exact hp
  · rintro ⟨C, hC, rfl⟩
    change echelonCoordinateProduct D (embedMatrix C) ∈
      embeddedRowMatrixModule (echelonRowSpace D) n
    choose w hw using fun i =>
      (mem_echelonDenominatorModule_iff D (C i)).1 (hC i)
    let B : IntegralMatrix K n m := fun i j => w i j
    apply (mem_embeddedRowMatrixModule_iff (echelonRowSpace D)
      (echelonCoordinateProduct D (embedMatrix C))).2
    refine ⟨B, ?_, ?_⟩
    · intro i
      apply (mem_echelonLambda_iff_exists_denominator_coeff D (B.row i)).2
      exact ⟨⟨C i, hC i⟩, hw i⟩
    · ext i j
      change numberEmbeddingRingHom K (w i j : K) =
        ∑ q : Fin k,
          numberEmbeddingRingHom K (C i q : K) *
            numberEmbeddingRingHom K ((D.1 : M k m K) q j)
      calc
        numberEmbeddingRingHom K (w i j : K) =
            numberEmbeddingRingHom K
              (∑ q : Fin k, (C i q : K) * (D.1 : M k m K) q j) :=
          congrArg (numberEmbeddingRingHom K) (hw i j)
        _ = ∑ q : Fin k,
            numberEmbeddingRingHom K
              ((C i q : K) * (D.1 : M k m K) q j) :=
          map_sum (numberEmbeddingRingHom K)
            (fun q : Fin k => (C i q : K) * (D.1 : M k m K) q j)
            Finset.univ
        _ = ∑ q : Fin k,
            numberEmbeddingRingHom K (C i q : K) *
              numberEmbeddingRingHom K ((D.1 : M k m K) q j) := by
          apply Finset.sum_congr rfl
          intro q hq
          exact map_mul (numberEmbeddingRingHom K) _ _

/- [Lean infrastructure, paper definition `de:denonimator`, lines 192--195]
The mixed-embedding realizations of the full coefficient module
`M_{n×k}(O_K)` and of its rowwise denominator submodule. -/
noncomputable def embeddedIntegralCoefficientLattice (n k : ℕ) :
    Submodule ℤ (M n k (K_ℝ[K])) :=
  ((⊤ : Submodule (𝓞 K) (IntegralMatrix K n k)).restrictScalars ℤ).map
    (integralMatrixEmbedding (K := K) n k)

/- [derived consequence, paper lines 661--674 and 844--848] Membership in
the full coefficient lattice is coordinatewise membership in the
mixed-embedded integer lattice.  This is the literal matrix-product form of
`O_K` under the manuscript embedding. -/
theorem mem_embeddedIntegralCoefficientLattice_iff
    {n k : ℕ} (x : M n k (K_ℝ[K])) :
    x ∈ embeddedIntegralCoefficientLattice (K := K) n k ↔
      ∀ i q, x i q ∈
        NumberField.mixedEmbedding.euclidean.integerLattice K := by
  constructor
  · rintro ⟨C, hC, rfl⟩ i q
    rw [NumberField.mixedEmbedding.euclidean.integerLattice]
    change NumberField.mixedEmbedding.euclidean.toMixed K
        (numberEmbedding K (C i q : K)) ∈
      NumberField.mixedEmbedding.integerLattice K
    exact ⟨C i q, by simp [numberEmbedding]⟩
  · intro hx
    choose C hC using fun i q =>
      (show ∃ a : 𝓞 K, numberEmbedding K (a : K) = x i q from by
        have hiq := hx i q
        rw [NumberField.mixedEmbedding.euclidean.integerLattice] at hiq
        change NumberField.mixedEmbedding.euclidean.toMixed K (x i q) ∈
          NumberField.mixedEmbedding.integerLattice K at hiq
        rw [NumberField.mixedEmbedding.integerLattice] at hiq
        obtain ⟨a, ha⟩ := hiq
        refine ⟨a, ?_⟩
        apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
        simpa [numberEmbedding] using ha)
    refine ⟨C, trivial, ?_⟩
    ext i q
    exact hC i q

/- [Lean infrastructure, paper lines 661--674] The full coefficient module
is discrete because it embeds continuously and injectively into the finite
product of copies of the mixed integer lattice. -/
noncomputable instance embeddedIntegralCoefficientLattice.discreteTopology
    (n k : ℕ) :
    DiscreteTopology (embeddedIntegralCoefficientLattice (K := K) n k) := by
  let L := NumberField.mixedEmbedding.euclidean.integerLattice K
  let _ : DiscreteTopology L := by
    dsimp [L]
    infer_instance
  let toProduct : embeddedIntegralCoefficientLattice (K := K) n k →
      (Fin n → Fin k → L) := fun x i q =>
    ⟨x.1 i q,
      (mem_embeddedIntegralCoefficientLattice_iff x.1).1 x.2 i q⟩
  apply DiscreteTopology.of_continuous_injective (f := toProduct)
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro q
    apply Continuous.subtype_mk
    exact (continuous_apply q).comp
      ((continuous_apply i).comp continuous_subtype_val)
  · intro x y hxy
    apply Subtype.ext
    ext i q
    exact congrArg Subtype.val (congrFun (congrFun hxy i) q)

/- [derived consequence, paper lines 661--674] The product integer module
spans the complete coefficient matrix space. -/
theorem embeddedIntegralCoefficientLattice_span_top (n k : ℕ) :
    Submodule.span ℝ
      (embeddedIntegralCoefficientLattice (K := K) n k :
        Set (M n k (K_ℝ[K]))) = ⊤ := by
  let L := NumberField.mixedEmbedding.euclidean.integerLattice K
  let S : Submodule ℝ (M n k (K_ℝ[K])) :=
    Submodule.span ℝ
      (embeddedIntegralCoefficientLattice (K := K) n k :
        Set (M n k (K_ℝ[K])))
  have hcoord : ∀ (i : Fin n) (q : Fin k) (x : K_ℝ[K]),
      x ∈ Submodule.span ℝ (L : Set (K_ℝ[K])) →
        Matrix.single i q x ∈ S := by
    intro i q x hx
    refine Submodule.span_induction (p := fun y _ =>
      Matrix.single i q y ∈ S) ?_ ?_ ?_ ?_ hx
    · intro y hy
      apply Submodule.subset_span
      apply (mem_embeddedIntegralCoefficientLattice_iff
        (K := K) (n := n) (k := k) (Matrix.single i q y)).2
      intro i' q'
      by_cases h : i = i' ∧ q = q'
      · rcases h with ⟨rfl, rfl⟩
        simpa using hy
      · change (if i = i' ∧ q = q' then y else 0) ∈ L
        rw [if_neg h]
        exact L.zero_mem
    · have hzero : Matrix.single i q (0 : K_ℝ[K]) =
          (0 : M n k (K_ℝ[K])) := by
        ext i' q'
        simp [Matrix.single]
      rw [hzero]
      exact S.zero_mem
    · intro x y _ _ hx hy
      have hadd := Matrix.single_add i q x y
      rw [hadd]
      exact S.add_mem hx hy
    · intro a x _ hx
      have hsmul : Matrix.single i q (a • x) =
          a • Matrix.single i q x := (Matrix.smul_single a i q x).symm
      rw [hsmul]
      exact S.smul_mem a hx
  rw [eq_top_iff]
  intro x hx
  have hdecomp : x =
      ∑ i : Fin n, ∑ q : Fin k, Matrix.single i q (x i q) := by
    exact Matrix.matrix_eq_sum_single x
  rw [hdecomp]
  apply S.sum_mem
  intro i hi
  apply S.sum_mem
  intro q hq
  apply hcoord i q (x i q)
  have hspan : Submodule.span ℝ (L : Set (K_ℝ[K])) = ⊤ :=
    IsZLattice.span_top (K := ℝ)
      (L := NumberField.mixedEmbedding.euclidean.integerLattice K)
  rw [hspan]
  trivial

noncomputable instance embeddedIntegralCoefficientLattice.isZLattice
    (n k : ℕ) :
    @IsZLattice ℝ inferInstance (M n k (K_ℝ[K]))
      inferInstance inferInstance
      (embeddedIntegralCoefficientLattice (K := K) n k)
      (embeddedIntegralCoefficientLattice.discreteTopology n k) :=
  @IsZLattice.mk ℝ inferInstance (M n k (K_ℝ[K]))
    inferInstance inferInstance
    (embeddedIntegralCoefficientLattice (K := K) n k)
    (embeddedIntegralCoefficientLattice.discreteTopology n k)
    (embeddedIntegralCoefficientLattice_span_top n k)

/- [Lean infrastructure, paper equation `eq:norm`, lines 661--674]
The Euclidean Hausdorff measure for the Frobenius realization of the
coefficient matrix space, with its measurable-space arguments fixed
explicitly as in `rowMatrixEuclideanMeasure`. -/
noncomputable def coefficientMatrixEuclideanMeasure (n k : ℕ) :
    @Measure (M n k (K_ℝ[K])) (kRealMatrixMeasurableSpace (K := K)) :=
  @Measure.euclideanHausdorffMeasure (M n k (K_ℝ[K]))
    inferInstance
    (kRealMatrixMeasurableSpace (K := K))
    (kRealMatrixBorelSpace (K := K))
    (Module.finrank ℝ (M n k (K_ℝ[K])))

noncomputable local instance coefficientMatrixEuclideanMeasure_isAddHaarMeasure
    (n k : ℕ) :
    Measure.IsAddHaarMeasure
      (coefficientMatrixEuclideanMeasure (K := K) n k) := by
  unfold coefficientMatrixEuclideanMeasure
  exact @MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure
    (M n k (K_ℝ[K])) inferInstance inferInstance inferInstance
    (kRealMatrixMeasurableSpace (K := K))
    (kRealMatrixBorelSpace (K := K))

theorem embeddedIntegralCoefficientLattice_covolume_euclidean_pos
    (n k : ℕ) :
    0 < ZLattice.covolume
      (embeddedIntegralCoefficientLattice (K := K) n k)
      (coefficientMatrixEuclideanMeasure (K := K) n k) := by
  exact @ZLattice.covolume_pos (M n k (K_ℝ[K])) inferInstance inferInstance
    inferInstance (kRealMatrixMeasurableSpace (K := K))
    (kRealMatrixBorelSpace (K := K))
    (embeddedIntegralCoefficientLattice (K := K) n k)
    (embeddedIntegralCoefficientLattice.discreteTopology n k)
    (embeddedIntegralCoefficientLattice.isZLattice n k)
    (coefficientMatrixEuclideanMeasure (K := K) n k)
    (coefficientMatrixEuclideanMeasure_isAddHaarMeasure (K := K) n k)

/- [Lean infrastructure, paper equation `eq:norm`, lines 661--674, and
`eq:value_of_c`, lines 197--202] The manuscript's Lebesgue measure on the
orthogonal product `M_{n×k}(K_ℝ)`, characterized exactly by requiring the
full coefficient lattice `M_{n×k}(O_K)` to have covolume one.  The paper's
discriminant-scaled metric has this normalization; in Lean we realize the
same measure as the unique positive scalar multiple of Euclidean volume with
that covolume. -/
noncomputable def paperMatrixMeasureScale (n k : ℕ) : NNReal :=
  ⟨(ZLattice.covolume
      (embeddedIntegralCoefficientLattice (K := K) n k)
      (coefficientMatrixEuclideanMeasure (K := K) n k))⁻¹,
    inv_nonneg.mpr
      (embeddedIntegralCoefficientLattice_covolume_euclidean_pos
        (K := K) n k).le⟩

theorem paperMatrixMeasureScale_pos (n k : ℕ) :
    0 < paperMatrixMeasureScale (K := K) n k := by
  letI : Measure.IsAddHaarMeasure
      (coefficientMatrixEuclideanMeasure (K := K) n k) :=
    coefficientMatrixEuclideanMeasure_isAddHaarMeasure (K := K) n k
  change 0 < (ZLattice.covolume
    (embeddedIntegralCoefficientLattice (K := K) n k)
    (coefficientMatrixEuclideanMeasure (K := K) n k))⁻¹
  exact inv_pos.mpr
    (embeddedIntegralCoefficientLattice_covolume_euclidean_pos
      (K := K) n k)

noncomputable def paperMatrixMeasure (n k : ℕ) :
    Measure (M n k (K_ℝ[K])) :=
  paperMatrixMeasureScale (K := K) n k •
    coefficientMatrixEuclideanMeasure (K := K) n k

/- [derived consequence, paper equation `eq:norm`, lines 661--674]
The manuscript product measure is additive Haar measure. -/
theorem paperMatrixMeasure_isAddHaarMeasure (n k : ℕ) :
    Measure.IsAddHaarMeasure (paperMatrixMeasure (K := K) n k) := by
  unfold paperMatrixMeasure
  letI : Measure.IsAddHaarMeasure
      (coefficientMatrixEuclideanMeasure (K := K) n k) :=
    coefficientMatrixEuclideanMeasure_isAddHaarMeasure (K := K) n k
  exact Measure.IsAddHaarMeasure.nnreal_smul
    (coefficientMatrixEuclideanMeasure (K := K) n k)
    (paperMatrixMeasureScale_pos (K := K) n k).ne'

/- [paper, equation `eq:norm`, lines 661--674] The full product lattice of
algebraic-integer coefficients has covolume one in the manuscript's product
Euclidean measure. -/
theorem embeddedIntegralCoefficientLattice_covolume_paperMatrixMeasure
    (n k : ℕ) :
    ZLattice.covolume
        (embeddedIntegralCoefficientLattice (K := K) n k)
        (paperMatrixMeasure (K := K) n k) = 1 := by
  letI : Measure.IsAddHaarMeasure
      (coefficientMatrixEuclideanMeasure (K := K) n k) :=
    coefficientMatrixEuclideanMeasure_isAddHaarMeasure (K := K) n k
  letI : Measure.IsAddHaarMeasure (paperMatrixMeasure (K := K) n k) :=
    paperMatrixMeasure_isAddHaarMeasure (K := K) n k
  have hscale : ZLattice.covolume
      (embeddedIntegralCoefficientLattice (K := K) n k)
      (paperMatrixMeasureScale (K := K) n k •
        coefficientMatrixEuclideanMeasure (K := K) n k) =
      (paperMatrixMeasureScale (K := K) n k : ℝ) *
        ZLattice.covolume
          (embeddedIntegralCoefficientLattice (K := K) n k)
          (coefficientMatrixEuclideanMeasure (K := K) n k) :=
    @covolume_nnreal_smul_measure (M n k (K_ℝ[K])) inferInstance
      inferInstance inferInstance (kRealMatrixMeasurableSpace (K := K))
      (kRealMatrixBorelSpace (K := K))
      (embeddedIntegralCoefficientLattice (K := K) n k)
      (embeddedIntegralCoefficientLattice.discreteTopology n k)
      (embeddedIntegralCoefficientLattice.isZLattice n k)
      (coefficientMatrixEuclideanMeasure (K := K) n k)
      (coefficientMatrixEuclideanMeasure_isAddHaarMeasure (K := K) n k)
      (paperMatrixMeasureScale (K := K) n k)
      (paperMatrixMeasureScale_pos (K := K) n k).ne'
  rw [paperMatrixMeasure, hscale]
  change (ZLattice.covolume
        (embeddedIntegralCoefficientLattice (K := K) n k)
        (coefficientMatrixEuclideanMeasure (K := K) n k))⁻¹ *
      ZLattice.covolume
        (embeddedIntegralCoefficientLattice (K := K) n k)
        (coefficientMatrixEuclideanMeasure (K := K) n k) = 1
  exact inv_mul_cancel₀
    (embeddedIntegralCoefficientLattice_covolume_euclidean_pos
      (K := K) n k).ne'

/- [derived consequence, paper equation `eq:norm`, lines 661--674]
The preceding covolume-one condition uniquely characterizes the manuscript
matrix measure among additive Haar measures.  This is the explicit bridge
ensuring that the normalized realization is not a measure substitution. -/
theorem eq_paperMatrixMeasure_of_covolume_eq_one
    (n k : ℕ) (mu : Measure (M n k (K_ℝ[K])))
    [Measure.IsAddHaarMeasure mu]
    (hmu : ZLattice.covolume
      (embeddedIntegralCoefficientLattice (K := K) n k) mu = 1) :
    mu = paperMatrixMeasure (K := K) n k := by
  letI : Measure.IsAddHaarMeasure (paperMatrixMeasure (K := K) n k) :=
    paperMatrixMeasure_isAddHaarMeasure (K := K) n k
  exact @isAddHaarMeasure_eq_of_lattice_covolume_eq_one
    (M n k (K_ℝ[K])) inferInstance inferInstance inferInstance
    (kRealMatrixMeasurableSpace (K := K))
    (kRealMatrixBorelSpace (K := K))
    (embeddedIntegralCoefficientLattice (K := K) n k)
    (embeddedIntegralCoefficientLattice.discreteTopology n k)
    (embeddedIntegralCoefficientLattice.isZLattice n k)
    mu (paperMatrixMeasure (K := K) n k) (by assumption)
    (paperMatrixMeasure_isAddHaarMeasure (K := K) n k) hmu
    (embeddedIntegralCoefficientLattice_covolume_paperMatrixMeasure
      (K := K) n k)

noncomputable def embeddedEchelonDenominatorLattice {n k m : ℕ}
    (D : EchelonMatrix K k m) : Submodule ℤ (M n k (K_ℝ[K])) :=
  ((echelonDenominatorMatrixModule (n := n) D).restrictScalars ℤ).map
    (integralMatrixEmbedding (K := K) n k)

/- [derived consequence, paper definition `de:denonimator`, lines 192--195]
The arithmetic mixed-embedding model of the denominator module is exactly
the analytic pullback lattice. -/
theorem embeddedEchelonDenominatorLattice_eq_coefficientZLattice
    {n k m : ℕ} (D : EchelonMatrix K k m) :
    embeddedEchelonDenominatorLattice (n := n) D =
      echelonCoefficientZLattice (n := n) D := by
  ext x
  rw [mem_echelonCoefficientZLattice_iff_exists_denominatorMatrix]
  constructor
  · rintro ⟨C, hC, hCx⟩
    exact ⟨C, hC, hCx⟩
  · rintro ⟨C, hC, hCx⟩
    exact ⟨C, hC, hCx⟩

/- [derived consequence, paper definition `de:denonimator`, lines 192--195]
The denominator lattice is a sublattice of the full integral coefficient
lattice. -/
theorem embeddedEchelonDenominatorLattice_le_integralCoefficientLattice
    {n k m : ℕ} (D : EchelonMatrix K k m) :
    embeddedEchelonDenominatorLattice (n := n) D ≤
      embeddedIntegralCoefficientLattice (K := K) n k := by
  intro x hx
  obtain ⟨C, hC, rfl⟩ := hx
  exact ⟨C, trivial, rfl⟩

/- [derived consequence, paper definition `de:denonimator`, lines 192--195]
The product denominator formula already proved in `Echelon.lean` survives
the injective mixed embedding.  This is the exact arithmetic index appearing
in manuscript line 845. -/
theorem embeddedEchelonDenominatorLattice_relIndex
    {n k m : ℕ} (D : EchelonMatrix K k m) :
    (embeddedEchelonDenominatorLattice (n := n) D).toAddSubgroup.relIndex
        (embeddedIntegralCoefficientLattice (K := K) n k).toAddSubgroup =
      echelonDenominator D ^ n := by
  let N : Submodule (𝓞 K) (IntegralMatrix K n k) :=
    echelonDenominatorMatrixModule (n := n) D
  let e := integralMatrixEmbedding (K := K) n k
  change
    (((N.restrictScalars ℤ).map e).toAddSubgroup.relIndex
      (((⊤ : Submodule (𝓞 K) (IntegralMatrix K n k)).restrictScalars ℤ).map e).toAddSubgroup) =
        echelonDenominator D ^ n
  rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective]
  · change N.toAddSubgroup.relIndex ⊤ = echelonDenominator D ^ n
    rw [AddSubgroup.relIndex_top_right]
    exact echelonDenominatorMatrixModule_index D
  · exact integralMatrixEmbedding_injective (K := K) n k

/- [derived consequence, paper definition `de:denonimator`, lines 192--195,
and equation `eq:d_D_defined`, lines 844--854] The exact index calculation,
together with the manuscript normalization of product Euclidean measure,
computes the covolume of the literal coefficient pullback lattice. -/
theorem echelonCoefficientZLattice_covolume_paperMatrixMeasure
    {n k m : ℕ} (D : EchelonMatrix K k m) :
    ZLattice.covolume (echelonCoefficientZLattice (n := n) D)
        (paperMatrixMeasure (K := K) n k) =
      (echelonDenominator D : ℝ) ^ n := by
  let L₁ := echelonCoefficientZLattice (n := n) D
  let L₂ := embeddedIntegralCoefficientLattice (K := K) n k
  let rowDisc : DiscreteTopology
      (rowMatrixZLattice (echelonRowSpace D) n) :=
    rowMatrixZLattice.discreteTopology (K := K) (n := n)
      (echelonRowSpace D)
  let rowZ : @IsZLattice ℝ inferInstance
      (rowMatrixRealSpan (echelonRowSpace D) n) inferInstance inferInstance
      (rowMatrixZLattice (echelonRowSpace D) n) rowDisc :=
    rowMatrixZLattice.isZLattice (K := K) (n := n)
      (echelonRowSpace D)
  let disc₁ : DiscreteTopology L₁ := by
    dsimp only [L₁, echelonCoefficientZLattice]
    exact @ZLattice.comap_discreteTopology ℝ inferInstance
      (rowMatrixRealSpan (echelonRowSpace D) n) (M n k (K_ℝ[K]))
      inferInstance inferInstance inferInstance inferInstance
      (rowMatrixZLattice (echelonRowSpace D) n) rowDisc
      (echelonCoordinateContinuousEquiv D).toLinearMap
      (echelonCoordinateContinuousEquiv D).continuous
      (echelonCoordinateContinuousEquiv D).injective
  let z₁ : @IsZLattice ℝ inferInstance (M n k (K_ℝ[K]))
      inferInstance inferInstance L₁ disc₁ := by
    dsimp only [L₁, echelonCoefficientZLattice]
    exact @instIsZLatticeComap ℝ inferInstance
      (rowMatrixRealSpan (echelonRowSpace D) n) (M n k (K_ℝ[K]))
      inferInstance inferInstance inferInstance inferInstance
      (rowMatrixZLattice (echelonRowSpace D) n) rowDisc rowZ
      (echelonCoordinateContinuousEquiv D)
  let disc₂ : DiscreteTopology L₂ :=
    embeddedIntegralCoefficientLattice.discreteTopology (K := K) n k
  let z₂ : @IsZLattice ℝ inferInstance (M n k (K_ℝ[K]))
      inferInstance inferInstance L₂ disc₂ :=
    embeddedIntegralCoefficientLattice.isZLattice (K := K) n k
  let mu : Measure (M n k (K_ℝ[K])) :=
    coefficientMatrixEuclideanMeasure (K := K) n k
  let vol₀ : @Measure (M n k (K_ℝ[K]))
      (kRealMatrixMeasurableSpace (K := K)) :=
    @volume (M n k (K_ℝ[K]))
      (@measureSpaceOfInnerProductSpace (M n k (K_ℝ[K])) inferInstance
        (mainTermMatrixInnerProductSpace (K := K)) inferInstance
        (kRealMatrixMeasurableSpace (K := K))
        (kRealMatrixBorelSpace (K := K)))
  letI : Measure.IsAddHaarMeasure mu := by
    dsimp only [mu]
    exact coefficientMatrixEuclideanMeasure_isAddHaarMeasure (K := K) n k
  have hle : L₁ ≤ L₂ := by
    dsimp only [L₁, L₂]
    rw [← embeddedEchelonDenominatorLattice_eq_coefficientZLattice
      (n := n) D]
    exact embeddedEchelonDenominatorLattice_le_integralCoefficientLattice
      (n := n) D
  have hmu : mu = vol₀ := by
    dsimp only [mu, coefficientMatrixEuclideanMeasure, vol₀]
    exact @InnerProductSpace.euclideanHausdorffMeasure_eq_volume
      (M n k (K_ℝ[K])) inferInstance
      (mainTermMatrixInnerProductSpace (K := K))
      (kRealMatrixMeasurableSpace (K := K))
      (kRealMatrixBorelSpace (K := K)) inferInstance
  have hratio : ZLattice.covolume L₁ mu / ZLattice.covolume L₂ mu =
      (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) := by
    rw [hmu]
    exact @ZLattice.covolume_div_covolume_eq_relIndex'
      (M n k (K_ℝ[K])) inferInstance
      (mainTermMatrixInnerProductSpace (K := K)) inferInstance
      (kRealMatrixMeasurableSpace (K := K))
      (kRealMatrixBorelSpace (K := K))
      L₁ L₂ disc₁ z₁ disc₂ z₂ hle
  have hindex : L₁.toAddSubgroup.relIndex L₂.toAddSubgroup =
      echelonDenominator D ^ n := by
    dsimp only [L₁, L₂]
    rw [← embeddedEchelonDenominatorLattice_eq_coefficientZLattice
      (n := n) D]
    exact embeddedEchelonDenominatorLattice_relIndex (n := n) D
  have hscale : ZLattice.covolume L₁
      (paperMatrixMeasure (K := K) n k) =
      (paperMatrixMeasureScale (K := K) n k : ℝ) *
        ZLattice.covolume L₁ mu := by
    rw [paperMatrixMeasure]
    exact @covolume_nnreal_smul_measure
      (M n k (K_ℝ[K])) inferInstance inferInstance inferInstance
      (kRealMatrixMeasurableSpace (K := K))
      (kRealMatrixBorelSpace (K := K)) L₁ disc₁ z₁ mu
      (coefficientMatrixEuclideanMeasure_isAddHaarMeasure (K := K) n k)
      (paperMatrixMeasureScale (K := K) n k)
      (paperMatrixMeasureScale_pos (K := K) n k).ne'
  rw [hscale]
  change (ZLattice.covolume L₂ mu)⁻¹ * ZLattice.covolume L₁ mu =
    (echelonDenominator D : ℝ) ^ n
  rw [mul_comm]
  change ZLattice.covolume L₁ mu / ZLattice.covolume L₂ mu = _
  rw [hratio, hindex, Nat.cast_pow]

/- [derived consequence, paper line 844] The Jacobian is absorbed exactly
by transporting the measure: the coefficient lattice and its image lattice
have equal covolume.  This is `ZLattice.covolume_comap` applied to the
measure-preserving coordinate equivalence. -/
theorem echelonCoefficientZLattice_covolume_eq_image {n k m : ℕ}
    (D : EchelonMatrix K k m) (mu : Measure (M n k (K_ℝ[K])))
    [Measure.IsAddHaarMeasure mu] :
    ZLattice.covolume (echelonCoefficientZLattice D) mu =
      ZLattice.covolume
        (rowMatrixZLattice (echelonRowSpace D) n)
        (echelonPushforwardMeasure D mu) := by
  let msW : MeasurableSpace
      (rowMatrixRealSpan (echelonRowSpace D) n) :=
    mainTermRowMatrixMeasurableSpace (echelonRowSpace D)
  let bsW : @BorelSpace
      (rowMatrixRealSpan (echelonRowSpace D) n) inferInstance msW :=
    @Subtype.borelSpace (M n m (K_ℝ[K])) inferInstance
      (kRealMatrixMeasurableSpace (K := K))
      (kRealMatrixBorelSpace (K := K))
      (fun A => A ∈ rowMatrixRealSpan (echelonRowSpace D) n)
  letI : MeasurableSpace
      (rowMatrixRealSpan (echelonRowSpace D) n) := msW
  letI : BorelSpace
      (rowMatrixRealSpan (echelonRowSpace D) n) := bsW
  letI : Measure.IsAddHaarMeasure (echelonPushforwardMeasure D mu) :=
    echelonPushforwardMeasure_isAddHaarMeasure D mu
  exact @ZLattice.covolume_comap
    (rowMatrixRealSpan (echelonRowSpace D) n)
    inferInstance inferInstance inferInstance msW bsW
    (rowMatrixZLattice (echelonRowSpace D) n)
    (rowMatrixZLattice.discreteTopology (echelonRowSpace D))
    (rowMatrixZLattice.isZLattice (echelonRowSpace D))
    (echelonPushforwardMeasure D mu)
    (echelonPushforwardMeasure_isAddHaarMeasure D mu)
    (M n k (K_ℝ[K])) inferInstance inferInstance inferInstance
    (kRealMatrixMeasurableSpace (K := K))
    (kRealMatrixBorelSpace (K := K)) mu (by assumption)
    (echelonCoordinateContinuousEquiv D)
    ⟨(echelonCoordinateContinuousEquiv D).continuous.measurable, rfl⟩

/- [derived consequence, paper equation `eq:d_D_defined`, lines 847--854]
The coordinate integral, divided by the covolume of the integral image
lattice in the transported measure, is exactly the existing row-space
summand.  This proves the full measure/Jacobian part of the normalization;
the denominator calculation below is a separate integral-lattice index
statement. -/
theorem echelon_normalized_coordinate_integral_eq_mainSummand {n k m : ℕ}
    (D : EchelonMatrix K k m) (mu : Measure (M n k (K_ℝ[K])))
    [Measure.IsAddHaarMeasure mu] (f : M n m (K_ℝ[K]) → ℝ) :
    (ZLattice.covolume
        (rowMatrixZLattice (echelonRowSpace D) n)
        (echelonPushforwardMeasure D mu))⁻¹ *
      (∫ x : M n k (K_ℝ[K]),
        f (echelonCoordinateProduct D x) ∂mu) =
      (rowMatrixLatticeCovolume (echelonRowSpace D) n)⁻¹ *
        rowMatrixSubspaceIntegral (echelonRowSpace D) n f := by
  letI : Measure.IsAddHaarMeasure (echelonPushforwardMeasure D mu) :=
    echelonPushforwardMeasure_isAddHaarMeasure D mu
  rw [← integral_echelonPushforwardMeasure D mu f]
  exact rowMatrixNormalizedIntegralWithMeasure_eq_mainSummand
    (echelonRowSpace D) (echelonPushforwardMeasure D mu) f

/- [derived consequence, paper equations `de:denonimator` and
`eq:d_D_defined`, lines 192--195 and 844--854] Once the exact covolume/index
identity is supplied, the preceding measure bridge becomes the manuscript's
literal factor `𝔇(D)⁻ⁿ`.  The hypothesis is deliberately an ordinary theorem
argument: it isolates the lattice-normalization obligation without hiding it
as an instance or axiom.  The required identity is proved and discharged in
the unconditional manuscript-facing theorem below. -/
theorem echelon_denominator_integral_eq_mainSummand_of_covolume_eq
    {n k m : ℕ} (D : EchelonMatrix K k m)
    (mu : Measure (M n k (K_ℝ[K]))) [Measure.IsAddHaarMeasure mu]
    (hcov : ZLattice.covolume
        (rowMatrixZLattice (echelonRowSpace D) n)
        (echelonPushforwardMeasure D mu) =
      (echelonDenominator D : ℝ) ^ n)
    (f : M n m (K_ℝ[K]) → ℝ) :
    (echelonDenominator D : ℝ)⁻¹ ^ n *
      (∫ x : M n k (K_ℝ[K]),
        f (echelonCoordinateProduct D x) ∂mu) =
      (rowMatrixLatticeCovolume (echelonRowSpace D) n)⁻¹ *
        rowMatrixSubspaceIntegral (echelonRowSpace D) n f := by
  have h := echelon_normalized_coordinate_integral_eq_mainSummand D mu f
  rw [hcov] at h
  simpa only [inv_pow] using h

/- [derived consequence, paper equations `de:denonimator` and
`eq:d_D_defined`, lines 192--195 and 844--854] Equivalent source-lattice
form of the denominator bridge.  After the pullback identification above,
the remaining arithmetic assertion is precisely that the coefficient
lattice has covolume `𝔇(D)^n` in the manuscript-normalized coordinate
measure. -/
theorem echelon_denominator_integral_eq_mainSummand_of_coefficient_covolume
    {n k m : ℕ} (D : EchelonMatrix K k m)
    (mu : Measure (M n k (K_ℝ[K]))) [Measure.IsAddHaarMeasure mu]
    (hcov : ZLattice.covolume (echelonCoefficientZLattice D) mu =
      (echelonDenominator D : ℝ) ^ n)
    (f : M n m (K_ℝ[K]) → ℝ) :
    (echelonDenominator D : ℝ)⁻¹ ^ n *
      (∫ x : M n k (K_ℝ[K]),
        f (echelonCoordinateProduct D x) ∂mu) =
      (rowMatrixLatticeCovolume (echelonRowSpace D) n)⁻¹ *
        rowMatrixSubspaceIntegral (echelonRowSpace D) n f := by
  apply echelon_denominator_integral_eq_mainSummand_of_covolume_eq D mu
  rw [← echelonCoefficientZLattice_covolume_eq_image D mu]
  exact hcov

/- [derived consequence, paper equation `eq:value_of_c`, lines 197--202]
The exact normalized coordinate summands reindex to `mainConstant` through
the manuscript's echelon/row-space trijection.  This proves the reindexing
part independently of the denominator computation. -/
theorem tsum_echelon_normalized_coordinate_integral_eq_mainConstant
    {n k m : ℕ} (mu : Measure (M n k (K_ℝ[K])))
    [Measure.IsAddHaarMeasure mu] (f : M n m (K_ℝ[K]) → ℝ) :
    (∑' D : EchelonMatrix K k m,
      (ZLattice.covolume
          (rowMatrixZLattice (echelonRowSpace D) n)
          (echelonPushforwardMeasure D mu))⁻¹ *
        (∫ x : M n k (K_ℝ[K]),
          f (echelonCoordinateProduct D x) ∂mu)) =
      mainConstant n m k f := by
  calc
    _ = ∑' D : EchelonMatrix K k m,
        (rowMatrixLatticeCovolume (echelonRowSpace D) n)⁻¹ *
          rowMatrixSubspaceIntegral (echelonRowSpace D) n f := by
      apply tsum_congr
      intro D
      exact echelon_normalized_coordinate_integral_eq_mainSummand D mu f
    _ = ∑' V : Grassmannian K m k,
        (rowMatrixLatticeCovolume V n)⁻¹ *
          rowMatrixSubspaceIntegral V n f := by
      rw [tsum_echelon_reindex_rowSpaces]
      apply tsum_congr
      intro V
      change
        (rowMatrixLatticeCovolume
            (echelonRowSpace
              ((echelonRowSpaceEquiv (K := K) (l := k) (m := m)).symm V)) n)⁻¹ *
            rowMatrixSubspaceIntegral
              (echelonRowSpace
                ((echelonRowSpaceEquiv (K := K) (l := k) (m := m)).symm V)) n f = _
      have hrow : echelonRowSpace
          ((echelonRowSpaceEquiv (K := K) (l := k) (m := m)).symm V) = V := by
        exact (echelonRowSpaceEquiv (K := K) (l := k) (m := m)).apply_symm_apply V
      rw [hrow]
    _ = mainConstant n m k f := rfl

/- [derived consequence, paper equation `eq:value_of_c`, lines 197--202]
Literal denominator form of the preceding reindexing theorem, conditional
only on the displayed covolume identity for each echelon representative.
This interface makes the denominator/index bridge auditable; the identity is
proved for `paperMatrixMeasure` and discharged in the unconditional theorem
immediately below. -/
theorem tsum_echelon_denominator_integral_eq_mainConstant_of_covolume_eq
    {n k m : ℕ} (mu : Measure (M n k (K_ℝ[K])))
    [Measure.IsAddHaarMeasure mu]
    (hcov : ∀ D : EchelonMatrix K k m,
      ZLattice.covolume
          (rowMatrixZLattice (echelonRowSpace D) n)
          (echelonPushforwardMeasure D mu) =
        (echelonDenominator D : ℝ) ^ n)
    (f : M n m (K_ℝ[K]) → ℝ) :
    (∑' D : EchelonMatrix K k m,
      (echelonDenominator D : ℝ)⁻¹ ^ n *
        (∫ x : M n k (K_ℝ[K]),
          f (echelonCoordinateProduct D x) ∂mu)) =
      mainConstant n m k f := by
  calc
    _ = ∑' D : EchelonMatrix K k m,
      (ZLattice.covolume
          (rowMatrixZLattice (echelonRowSpace D) n)
          (echelonPushforwardMeasure D mu))⁻¹ *
        (∫ x : M n k (K_ℝ[K]),
          f (echelonCoordinateProduct D x) ∂mu) := by
      apply tsum_congr
      intro D
      rw [hcov D, inv_pow]
    _ = mainConstant n m k f :=
      tsum_echelon_normalized_coordinate_integral_eq_mainConstant mu f

/- [paper, equation `eq:value_of_c`, lines 197--202] Exact manuscript
formula for the main constant.  The coordinate measure is the product Haar
measure normalized so that `M_{n×k}(𝓞_K)` has covolume one, as required by
equation `eq:norm`; the proved denominator-module index supplies the factor
`𝔇(D)⁻ⁿ`, and `echelonRowSpaceEquiv` performs the manuscript's echelon
reindexing. -/
theorem tsum_echelon_denominator_integral_eq_mainConstant
    {n k m : ℕ} (f : M n m (K_ℝ[K]) → ℝ) :
    (∑' D : EchelonMatrix K k m,
      (echelonDenominator D : ℝ)⁻¹ ^ n *
        (∫ x : M n k (K_ℝ[K]),
          f (echelonCoordinateProduct D x)
            ∂paperMatrixMeasure (K := K) n k)) =
      mainConstant n m k f := by
  letI : Measure.IsAddHaarMeasure (paperMatrixMeasure (K := K) n k) :=
    paperMatrixMeasure_isAddHaarMeasure (K := K) n k
  apply tsum_echelon_denominator_integral_eq_mainConstant_of_covolume_eq
    (paperMatrixMeasure (K := K) n k)
  intro D
  rw [← echelonCoefficientZLattice_covolume_eq_image D
    (paperMatrixMeasure (K := K) n k)]
  exact echelonCoefficientZLattice_covolume_paperMatrixMeasure D

/- [paper, Lemma `le:schmidt_makes_c1_finite`, lines 832--859] The
manuscript's literal echelon-indexed series is absolutely summable when
`n > m`.  Schmidt's height count is exposed as the attributed
`HasHeightCountBounds` hypothesis; the bound on subspace integrals and the
denominator/Jacobian identity are proved locally. -/
theorem summable_echelon_denominator_integral_of_height_count
    {n k m : ℕ} (hnm : m < n) (hk : 0 < k)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f) :
    Summable (fun D : EchelonMatrix K k m =>
      (echelonDenominator D : ℝ)⁻¹ ^ n *
        (∫ x : M n k (K_ℝ[K]),
          f (echelonCoordinateProduct D x)
            ∂paperMatrixMeasure (K := K) n k)) := by
  have hn : 0 < n := by omega
  obtain ⟨C, hC, hdom⟩ :=
    h_f.exists_uniform_mainSummand_integral_domination f hn hk
  have hs : Summable (fun V : Grassmannian K m k =>
      (rowMatrixLatticeCovolume V n)⁻¹ *
        rowMatrixSubspaceIntegral V n f) :=
    summable_mainConstant_terms_of_height_count hnm hcount hC hdom
  let e := echelonRowSpaceEquiv (K := K) (l := k) (m := m)
  have hs' := hs.comp_injective e.injective
  letI : Measure.IsAddHaarMeasure (paperMatrixMeasure (K := K) n k) :=
    paperMatrixMeasure_isAddHaarMeasure (K := K) n k
  apply hs'.congr
  intro D
  have hterm :=
    echelon_denominator_integral_eq_mainSummand_of_coefficient_covolume
      D (paperMatrixMeasure (K := K) n k)
        (echelonCoefficientZLattice_covolume_paperMatrixMeasure D) f
  have heD : e D = echelonRowSpace D := rfl
  simpa only [Function.comp_apply, heD] using hterm.symm

/- [paper, Theorem `th:higher_moments`, equation
`eq:right_side_converge`, lines 1947--1964] The manuscript's limiting
echelon-integral sum, with its unique rank-zero contribution evaluated as
`f 0` and ranks `1, …, m` indexed by `Fin m`.  This retains the literal
denominator and coordinate integral for every positive-rank echelon matrix. -/
noncomputable def manuscriptEchelonIntegralLimit
    (n m : ℕ) (f : M n m (K_ℝ[K]) → ℝ) : ℝ :=
  f 0 + ∑ k : Fin m,
    ∑' D : EchelonMatrix K (k.1 + 1) m,
      (echelonDenominator D : ℝ)⁻¹ ^ n *
        (∫ x : M n (k.1 + 1) (K_ℝ[K]),
          f (echelonCoordinateProduct D x)
            ∂paperMatrixMeasure (K := K) n (k.1 + 1))

/- [derived consequence of paper equation `eq:value_of_c`, lines 197--202,
and Theorem `th:higher_moments`, lines 1947--1964] The row-space limit used
internally is exactly the manuscript's echelon-integral expression. -/
theorem manuscriptEchelonIntegralLimit_eq_echelonIntegralLimit
    (n m s : ℕ) (f : M n m (K_ℝ[K]) → ℝ) :
    manuscriptEchelonIntegralLimit (K := K) n m f =
      echelonIntegralLimit n m s f := by
  unfold manuscriptEchelonIntegralLimit echelonIntegralLimit
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact tsum_echelon_denominator_integral_eq_mainConstant f

end

end Katznelson
