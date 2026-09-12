import Katznelson.Counting.RiemannSum
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Geometry of numbers

This file contains the Euclidean geometry-of-numbers input used by the
manuscript.  The height of a full lattice is its covolume, and the first
Minkowski estimate is obtained from Mathlib's convex-body theorem applied to
a closed Euclidean ball.  The constant is left in the paper's form: it may
depend on the real dimension, but not on the lattice.

The Hadamard interface is recorded below in terms of the norm determinant of a
real basis.  Its proof is intentionally kept separate from the Minkowski
argument, since it is a basis estimate rather than a lattice-counting input.
-/

namespace Katznelson

open MeasureTheory Set Metric Module
open InnerProductSpace
open scoped Classical MeasureTheory Pointwise RealInnerProductSpace

section Minkowski

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

noncomputable def minkowskiUnitBallVolume : ℝ :=
  volume.real (closedBall (0 : E) 1)

theorem minkowskiUnitBallVolume_pos : 0 < minkowskiUnitBallVolume (E := E) := by
  dsimp [minkowskiUnitBallVolume]
  have hball : 0 < volume (ball (0 : E) 1) :=
    measure_ball_pos volume (0 : E) zero_lt_one
  have hclosed : volume (closedBall (0 : E) 1) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  have hreal : 0 < volume.real (ball (0 : E) 1) := by
    exact ENNReal.toReal_pos hball.ne' measure_ball_lt_top.ne
  have hreal_le : volume.real (ball (0 : E) 1) ≤
      volume.real (closedBall (0 : E) 1) := by
    exact MeasureTheory.measureReal_mono (ball_subset_closedBall)
  exact lt_of_lt_of_le hreal hreal_le

noncomputable def minkowskiConstant : ℝ :=
  ((2 : ℝ) ^ Module.finrank ℝ E /
      minkowskiUnitBallVolume (E := E)) ^
    (1 / (Module.finrank ℝ E : ℝ))

theorem minkowskiConstant_pos : 0 < minkowskiConstant (E := E) := by
  apply Real.rpow_pos_of_pos
  exact div_pos (by positivity) (minkowskiUnitBallVolume_pos (E := E))

/- [Lean infrastructure] The Euclidean unit-ball volume is determined by the
   real dimension.  This lets the first Minkowski constant be made uniform
   over the varying row spaces of one fixed Grassmannian; it is not a
   replacement for the successive-minima product estimate from
   Fieker--Stehlé. -/
theorem minkowskiUnitBallVolume_eq_of_finrank_eq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [Nontrivial F]
    (hfin : Module.finrank ℝ E = Module.finrank ℝ F) :
    minkowskiUnitBallVolume (E := E) = minkowskiUnitBallVolume (E := F) := by
  unfold minkowskiUnitBallVolume
  change (volume (closedBall (0 : E) 1)).toReal =
    (volume (closedBall (0 : F) 1)).toReal
  rw [InnerProductSpace.volume_closedBall, InnerProductSpace.volume_closedBall]
  simp [hfin]

/- [Lean infrastructure] Consequently the first Minkowski constant is also
   determined by the real dimension.  The statement is deliberately kept at
   the generic Euclidean-lattice level for later use in the rank-one case of
   the cited Fieker--Stehlé theorem. -/
theorem minkowskiConstant_eq_of_finrank_eq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [Nontrivial F]
    (hfin : Module.finrank ℝ E = Module.finrank ℝ F) :
    minkowskiConstant (E := E) = minkowskiConstant (E := F) := by
  unfold minkowskiConstant
  rw [minkowskiUnitBallVolume_eq_of_finrank_eq (E := E) hfin, hfin]

/- [Lean infrastructure] This elementary real-power identity is the
   normalization calculation behind the Euclidean first Minkowski constant.
   It is stated publicly because the supporting proof of the
   Fieker--Stehlé product estimate needs exactly the same calculation. -/
theorem rpow_one_over_finrank_pow
    (x : ℝ) (hx : 0 < x) :
    (x ^ (1 / (Module.finrank ℝ E : ℝ))) ^ Module.finrank ℝ E = x := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (le_of_lt hx)]
  have hdim : (Module.finrank ℝ E : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Module.finrank_pos (R := ℝ) (M := E)))
  field_simp
  simp

/- [Lean infrastructure] This is the volume normalization used in the first
   Minkowski theorem.  It is kept available for the later, standard
   Minkowski-II supporting argument; it does not change the manuscript's
   lattice or height normalization. -/
theorem minkowskiRadius_volume_identity
    {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : 0 < ZLattice.covolume L)
    (R : ℝ) (hR : R = minkowskiConstant (E := E) *
      (ZLattice.covolume L) ^ (1 / (Module.finrank ℝ E : ℝ))) :
    R ^ Module.finrank ℝ E * minkowskiUnitBallVolume (E := E) =
      ZLattice.covolume L * (2 : ℝ) ^ Module.finrank ℝ E := by
  rw [hR, mul_pow]
  have hconst := rpow_one_over_finrank_pow
    (E := E) (((2 : ℝ) ^ Module.finrank ℝ E /
      minkowskiUnitBallVolume (E := E)))
    (div_pos (by positivity) (minkowskiUnitBallVolume_pos (E := E)))
  have hheight := rpow_one_over_finrank_pow
    (E := E) (ZLattice.covolume L)
    hL
  rw [show minkowskiConstant (E := E) =
      (((2 : ℝ) ^ Module.finrank ℝ E /
        minkowskiUnitBallVolume (E := E)) ^
          (1 / (Module.finrank ℝ E : ℝ))) by rfl]
  rw [hconst, hheight]
  have hunit := minkowskiUnitBallVolume_pos (E := E)
  field_simp

theorem exists_nonzero_latticeVector_norm_le_covolume_rpow
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ v : L, v ≠ 0 ∧
      ‖(v : E)‖ ≤ minkowskiConstant (E := E) *
        (ZLattice.covolume L) ^
          (1 / (Module.finrank ℝ E : ℝ)) := by
  let F : Set E := latticeFundamentalDomain L
  have hfundSub : IsAddFundamentalDomain L F (volume : Measure E) := by
    exact latticeFundamentalDomain_isAddFundamentalDomain L volume
  have hspan : Submodule.span ℤ (Set.range (latticeRealBasis L)) = L := by
    simpa [latticeRealBasis] using
      (latticeBasis L).ofZLatticeBasis_span ℝ
  have hfund' : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (latticeRealBasis L))).toAddSubgroup
      F (volume : Measure E) := by
    exact ZSpan.isAddFundamentalDomain' (latticeRealBasis L) volume
  letI : Countable (Submodule.span ℤ (Set.range (latticeRealBasis L))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range (latticeRealBasis L)))
    infer_instance
  have hFtop : volume F ≠ ⊤ := by
    exact (latticeFundamentalDomain_isBounded L).measure_lt_top.ne
  have hcov : 0 < ZLattice.covolume L := ZLattice.covolume_pos L
  let R : ℝ := minkowskiConstant (E := E) *
    (ZLattice.covolume L) ^ (1 / (Module.finrank ℝ E : ℝ))
  have hR : 0 < R := by
    dsimp [R]
    exact mul_pos (minkowskiConstant_pos (E := E))
      (Real.rpow_pos_of_pos hcov _)
  have hvolreal : volume.real (closedBall (0 : E) R) =
      R ^ Module.finrank ℝ E * minkowskiUnitBallVolume (E := E) := by
    rw [MeasureTheory.Measure.addHaar_real_closedBall' volume (0 : E) hR.le]
    rfl
  have hidentity : R ^ Module.finrank ℝ E *
      minkowskiUnitBallVolume (E := E) =
        ZLattice.covolume L * (2 : ℝ) ^ Module.finrank ℝ E := by
    exact minkowskiRadius_volume_identity (E := E) hcov R rfl
  have hballreal : volume.real (closedBall (0 : E) R) =
      ZLattice.covolume L * (2 : ℝ) ^ Module.finrank ℝ E :=
    hvolreal.trans hidentity
  have hfundcovol : ZLattice.covolume L = volume.real F :=
    ZLattice.covolume_eq_measure_fundamentalDomain L volume hfundSub
  have hbodyreal : volume.real F * (2 : ℝ) ^ Module.finrank ℝ E ≤
      volume.real (closedBall (0 : E) R) := by
    calc
      volume.real F * (2 : ℝ) ^ Module.finrank ℝ E =
          ZLattice.covolume L * (2 : ℝ) ^ Module.finrank ℝ E := by
        rw [hfundcovol]
      _ ≤ volume.real (closedBall (0 : E) R) := le_of_eq hballreal.symm
  have hballtop : volume (closedBall (0 : E) R) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  have hbody : volume F * (2 : ENNReal) ^ Module.finrank ℝ E ≤
      volume (closedBall (0 : E) R) := by
    have hbodytop : volume F * (2 : ENNReal) ^ Module.finrank ℝ E ≠ ⊤ := by
      exact ENNReal.mul_ne_top hFtop (by finiteness)
    refine (ENNReal.toReal_le_toReal hbodytop hballtop).mp ?_
    simpa [MeasureTheory.measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofNat, ENNReal.toReal_pow] using hbodyreal
  have hsymm : ∀ x ∈ closedBall (0 : E) R, -x ∈ closedBall (0 : E) R := by
    intro x hx
    simpa [mem_closedBall_zero_iff, norm_neg] using hx
  obtain ⟨v, hv, hvball⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      hfund' hsymm (convex_closedBall (0 : E) R)
      (isCompact_closedBall (0 : E) R) hbody
  have hvLmem : (v : E) ∈ L := by
    simpa [hspan] using v.property
  refine ⟨⟨(v : E), hvLmem⟩, ?_, ?_⟩
  · intro hvzero
    apply hv
    exact Subtype.ext (congrArg (fun x : L => (x : E)) hvzero)
  simpa [mem_closedBall_zero_iff, R] using hvball

end Minkowski

section ShortestVector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/- The first minimum in the real full-lattice specialization of the paper's
   Definition `de:defi_of_successive` is attained.  The number-field
   successive minima themselves are handled separately below; this theorem
   records only the discrete finite-ball argument used for the first step. -/
theorem exists_shortest_nonzero_latticeVector
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ v : L, v ≠ 0 ∧ ∀ w : L, w ≠ 0 → ‖(v : E)‖ ≤ ‖(w : E)‖ := by
  have hLbot : L ≠ ⊥ := by
    intro hL
    have hspan : Submodule.span ℝ (L : Set E) = ⊤ :=
      IsZLattice.span_top (K := ℝ) (L := L)
    rw [hL] at hspan
    simpa using hspan
  obtain ⟨v₀, hv₀L, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLbot
  let v₀' : L := ⟨v₀, hv₀L⟩
  let S : Set L := {v | v ≠ 0 ∧ ‖(v : E)‖ ≤ ‖(v₀' : E)‖}
  have hSfinite : S.Finite := by
    apply (lattice_ball_finite L).subset
    intro v hv
    exact hv.2
  have hv₀' : v₀' ≠ 0 := by
    intro h
    exact hv₀ (congrArg (fun x : L => (x : E)) h)
  have hSnonempty : S.Nonempty := ⟨v₀', hv₀', le_rfl⟩
  obtain ⟨v, hvS, hmin⟩ :=
    Set.exists_min_image S (fun w : L => ‖(w : E)‖) hSfinite hSnonempty
  refine ⟨v, hvS.1, ?_⟩
  intro w hw
  by_cases hbound : ‖(w : E)‖ ≤ ‖(v₀' : E)‖
  · exact hmin w ⟨hw, hbound⟩
  · exact (hvS.2.trans_lt (lt_of_not_ge hbound)).le

/- The shortest vector therefore satisfies the first Minkowski bound, which
   is the role of `l_1` in the proof of `le:props_of_minima` (lines 930--933). -/
theorem exists_shortest_nonzero_latticeVector_norm_le_covolume_rpow
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ v : L, v ≠ 0 ∧
      ‖(v : E)‖ ≤ minkowskiConstant (E := E) *
        (ZLattice.covolume L) ^
          (1 / (Module.finrank ℝ E : ℝ)) := by
  obtain ⟨v, hv, hmin⟩ := exists_shortest_nonzero_latticeVector L
  obtain ⟨w, hw, hbound⟩ :=
    exists_nonzero_latticeVector_norm_le_covolume_rpow L
  exact ⟨v, hv, (hmin w hw).trans hbound⟩

end ShortestVector

section Hadamard

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- The determinant estimate underlying the paper's Hadamard inequality. -/
theorem orthonormal_basis_det_le_prod_norm
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (b' : Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    |b.toBasis.det b'| ≤ ∏ i, ‖b' i‖ := by
  let g : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
    gramSchmidtOrthonormalBasis (by simp) (b' : Fin (Module.finrank ℝ E) → E)
  have hdet : b.toBasis.det (b' : Fin (Module.finrank ℝ E) → E) =
      b.toBasis.det (g : Fin (Module.finrank ℝ E) → E) *
        g.toBasis.det (b' : Fin (Module.finrank ℝ E) → E) := by
    exact (Basis.det_mul_det b.toBasis g.toBasis b').symm
  have hchange : |b.toBasis.det (g : Fin (Module.finrank ℝ E) → E)| = 1 := by
    have hchange' :=
      OrthonormalBasis.det_to_matrix_orthonormalBasis (a := b) (b := g)
    change ‖b.toBasis.det (g : Fin (Module.finrank ℝ E) → E)‖ = 1 at hchange'
    simpa only [Real.norm_eq_abs] using hchange'
  have hgs := gramSchmidtOrthonormalBasis_det
      (ι := Fin (Module.finrank ℝ E)) (𝕜 := ℝ) (E := E) (by simp)
      (b' : Fin (Module.finrank ℝ E) → E)
  rw [hdet, abs_mul, hchange, one_mul, hgs, Finset.abs_prod]
  calc
    ∏ i, |⟪g i, b' i⟫_ℝ| ≤ ∏ i, (‖g i‖ * ‖b' i‖) := by
      exact Finset.prod_le_prod (fun i hi => abs_nonneg _) (fun i hi =>
        abs_real_inner_le_norm _ _)
    _ = ∏ i, ‖b' i‖ := by
      simp [g.orthonormal.norm_eq_one]

/- The paper's Definition `de:hadamard_ratio` (lines 501--508), with
   `ZLattice.covolume L` realizing its height `H(Λ)` (lines 412--420). -/
noncomputable def hadamardRatio
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin (Module.finrank ℝ E)) ℤ L) : ℝ :=
  (∏ i, ‖(b i : E)‖) / ZLattice.covolume L

/- The paper's Lemma `le:hadamard_bound` (lines 512--519). -/
theorem one_le_hadamardRatio
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin (Module.finrank ℝ E)) ℤ L) :
    1 ≤ hadamardRatio L b := by
  let b0 : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
    stdOrthonormalBasis ℝ E
  let bR : Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    b.ofZLatticeBasis ℝ L
  have hmeasure : volume.real (ZSpan.fundamentalDomain b0.toBasis) = 1 := by
    rw [measureReal_congr
      (ZSpan.fundamentalDomain_ae_parallelepiped b0.toBasis volume)]
    change volume.real (parallelepiped b0) = 1
    simp [MeasureTheory.measureReal_def, OrthonormalBasis.volume_parallelepiped]
  have hcov := ZLattice.covolume_eq_det_mul_measureReal L volume b b0.toBasis
  rw [hmeasure, mul_one] at hcov
  have hdet : |b0.toBasis.det bR| ≤ ∏ i, ‖bR i‖ :=
    orthonormal_basis_det_le_prod_norm b0 bR
  have hvec : (Subtype.val ∘ ⇑b) = ⇑bR := by
    funext i
    simp [bR]
  rw [hvec] at hcov
  have hnorm : (∏ i, ‖bR i‖) = ∏ i, ‖(b i : E)‖ := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [bR]
  have hdet_cov : ZLattice.covolume L (volume : Measure E) ≤
      ∏ i, ‖(b i : E)‖ := by
    calc
      ZLattice.covolume L (volume : Measure E) = |b0.toBasis.det bR| := hcov
      _ ≤ ∏ i, ‖bR i‖ := hdet
      _ = ∏ i, ‖(b i : E)‖ := hnorm
  change 1 ≤ (∏ i, ‖(b i : E)‖) / ZLattice.covolume L (volume : Measure E)
  have hpos : 0 < ZLattice.covolume L (volume : Measure E) :=
    ZLattice.covolume_pos L volume
  rw [le_div_iff₀ hpos]
  simpa using hdet_cov

end Hadamard

/- [Lean infrastructure, used for the paper step `le:low_rank_induction`,
   lines 1452--1455]
   A spanning set contains a finite-dimensional complement to a subspace.
   The selected vectors are elements of the original set, and the conclusion
   is expressed by the quotient map.  This is the abstract linear-algebra
   content of choosing the vectors `l_j^(i)`; the later paper-facing instance
   must still prove that its bounded set spans the relevant row space. -/
theorem exists_fin_basis_extension_from_spanningSet
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E]
    (U : Submodule K E) (S : Set E)
    (hspan : Submodule.span K S = ⊤) {q : ℕ}
    (hq : Module.finrank K (E ⧸ U) = q) :
    ∃ v : Fin q → S,
      U ⊔ Submodule.span K (Set.range (fun i => (v i : E))) = ⊤ := by
  let Q : Set (E ⧸ U) := Submodule.Quotient.mk '' S
  have hQspan : Submodule.span K Q = ⊤ := by
    change Submodule.span K (Submodule.Quotient.mk '' S) = ⊤
    have hmap : Submodule.map U.mkQ (Submodule.span K S) = ⊤ := by
      rw [hspan, Submodule.map_top]
      exact (LinearMap.range_eq_top.mpr
        (Submodule.Quotient.mk_surjective U))
    rw [Submodule.map_span] at hmap
    exact hmap
  let bQ : Module.Basis
      ((linearIndepOn_empty K id).extend (empty_subset Q))
      K (E ⧸ U) := Module.Basis.ofSpan (hQspan.ge)
  let I := (linearIndepOn_empty K id).extend (empty_subset Q)
  letI : Fintype I := Fintype.ofFinite I
  have hcard : Fintype.card I = q := by
    calc
      Fintype.card I = Module.finrank K (E ⧸ U) := by
        symm
        exact Module.finrank_eq_card_basis bQ
      _ = q := hq
  let e : I ≃ Fin q := Fintype.equivFinOfCardEq hcard
  have hbQmem (j : I) : bQ j ∈ Q := by
    exact Module.Basis.ofSpan_subset (hQspan.ge) ⟨j, rfl⟩
  choose lift hlift using hbQmem
  have hlift_mk (j : I) :
      Submodule.Quotient.mk (lift j) = bQ j := by
    exact (hlift j).2
  let v : Fin q → S := fun i =>
    ⟨lift (e.symm i), (hlift (e.symm i)).1⟩
  have hmap : Submodule.map U.mkQ
      (Submodule.span K (Set.range (fun j : I => (lift j : E)))) = ⊤ := by
    rw [Submodule.map_span]
    have himage : Submodule.Quotient.mk ''
        Set.range (fun j : I => (lift j : E)) = Set.range bQ := by
      ext x
      constructor
      · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
        exact ⟨j, (hlift_mk j).symm⟩
      · rintro ⟨j, rfl⟩
        exact ⟨lift j, ⟨j, rfl⟩, hlift_mk j⟩
    change Submodule.span K
      (Submodule.Quotient.mk '' Set.range
        (fun j : I => (lift j : E))) = ⊤
    rw [himage]
    exact bQ.span_eq
  have hsum : U ⊔ Submodule.span K
      (Set.range (fun j : I => (lift j : E))) = ⊤ :=
    (Submodule.map_mkQ_eq_top U
      (Submodule.span K (Set.range (fun j : I => (lift j : E))))) |>.mp hmap
  have hrange : Set.range (fun i : Fin q => (v i : E)) =
      Set.range (fun j : I => (lift j : E)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by rfl⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨i, rfl⟩ := e.symm.surjective j
      exact ⟨i, by rfl⟩
  refine ⟨v, ?_⟩
  rw [hrange]
  exact hsum

/- [Lean infrastructure, used for the paper step `le:low_rank_induction`,
   line 1455]  Equality of the quotient spans of two complements forces
   equality of the ambient subspaces.  This is the abstract linear-algebra
   content of the paper's assertion that two row spaces are equal exactly
   when the corresponding tuples have equal spans modulo the lower-rank
   space. -/
theorem sup_eq_of_quotient_map_eq
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (U V W : Submodule K E) (S₁ S₂ : Set E)
    (hUV : U ≤ V) (hUW : U ≤ W)
    (hV : U ⊔ Submodule.span K S₁ = V)
    (hW : U ⊔ Submodule.span K S₂ = W)
    (hquot : Submodule.map U.mkQ (Submodule.span K S₁) =
      Submodule.map U.mkQ (Submodule.span K S₂)) :
    V = W := by
  apply le_antisymm
  · intro x hx
    rw [← hV] at hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, y, hy, hxy⟩
    have hquotx : U.mkQ y ∈
        Submodule.map U.mkQ (Submodule.span K S₂) := by
      rw [← hquot]
      exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩
    rcases Submodule.mem_map.mp hquotx with ⟨z, hz, hzy⟩
    have hdiff : y - z ∈ U := by
      apply (Submodule.Quotient.mk_eq_zero U).mp
      change U.mkQ y - U.mkQ z = 0
      rw [hzy]
      simp
    have hzW : z ∈ W := by
      rw [← hW]
      exact Submodule.mem_sup_right hz
    rw [← hxy]
    apply W.add_mem (hUW hu)
    rw [← sub_add_cancel y z]
    exact W.add_mem (hUW hdiff) hzW
  · intro x hx
    rw [← hW] at hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, y, hy, hxy⟩
    have hquotx : U.mkQ y ∈
        Submodule.map U.mkQ (Submodule.span K S₁) := by
      rw [hquot]
      exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩
    rcases Submodule.mem_map.mp hquotx with ⟨z, hz, hzy⟩
    have hdiff : y - z ∈ U := by
      apply (Submodule.Quotient.mk_eq_zero U).mp
      change U.mkQ y - U.mkQ z = 0
      rw [hzy]
      simp
    have hzV : z ∈ V := by
      rw [← hV]
      exact Submodule.mem_sup_right hz
    rw [← hxy]
    apply V.add_mem (hUV hu)
    rw [← sub_add_cancel y z]
    exact V.add_mem (hUV hdiff) hzV

/- [Lean infrastructure, used for the paper step `le:low_rank_induction`,
   lines 1452--1479]  Equality after orthogonal projection onto the
   complement of `U` is equivalent to equality modulo `U`.  This is the
   real-vector-space part of the paper's passage from selected vectors to
   their projected representatives.  The number-field identification of
   this real quotient with the K-row-space quotient is a separate bridge. -/
theorem orthogonalProjectionOnto_eq_iff_sub_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    [Uᗮ.HasOrthogonalProjection] {x y : E} :
    Uᗮ.orthogonalProjectionOnto x = Uᗮ.orthogonalProjectionOnto y ↔
      x - y ∈ U := by
  constructor
  · intro hxy
    have hp : Uᗮ.orthogonalProjectionOnto (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hmem : x - y ∈ Uᗮᗮ :=
      (Submodule.orthogonalProjectionOnto_eq_zero_iff).mp hp
    simpa using hmem
  · intro hxy
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero hxy

/- [Lean infrastructure, used for the paper step `le:low_rank_induction`,
   line 1455]  Pointwise equality of finitely or infinitely indexed tuples
   modulo `U` gives equality of the quotient spans.  This is the bookkeeping
   step that turns the paper's equality of projected tuples into the quotient
   equality consumed by `sup_eq_of_quotient_map_eq`. -/
theorem quotient_map_span_range_eq_of_forall
    {K E ι : Type*} [Field K] [AddCommGroup E] [Module K E]
    (U : Submodule K E) (x y : ι → E)
    (hxy : ∀ i, U.mkQ (x i) = U.mkQ (y i)) :
    Submodule.map U.mkQ (Submodule.span K (Set.range x)) =
      Submodule.map U.mkQ (Submodule.span K (Set.range y)) := by
  have himage : U.mkQ '' Set.range x = U.mkQ '' Set.range y := by
    ext z
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨y i, ⟨i, rfl⟩, (hxy i).symm⟩
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, hxy i⟩
  rw [Submodule.map_span, Submodule.map_span, himage]

/- [Lean infrastructure, used for the paper step `le:low_rank_induction`,
   lines 1452--1455]  Convert a complement equation in the subtype `V`
   back to the ambient row-space equation.  This is the bridge needed after
   selecting the paper's vectors inside the lower-containing row space. -/
theorem sup_eq_of_comap_sup_span_eq_top
    {K E ι : Type*} [Field K] [AddCommGroup E] [Module K E]
    (U V : Submodule K E) (hUV : U ≤ V) (x : ι → V)
    (hsup : U.comap V.subtype ⊔ Submodule.span K (Set.range x) = ⊤) :
    U ⊔ Submodule.span K (Set.range (fun i => (x i : E))) = V := by
  let W : Submodule K E := U ⊔ Submodule.span K
    (Set.range (fun i => (x i : E)))
  have hWle : W ≤ V := by
    apply sup_le hUV
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    exact (x i).property
  apply le_antisymm hWle
  intro y hy
  let yV : V := ⟨y, hy⟩
  have hyV : yV ∈ U.comap V.subtype ⊔ Submodule.span K (Set.range x) := by
    rw [hsup]
    exact Submodule.mem_top
  rcases (Submodule.mem_sup.mp hyV) with ⟨u, hu, z, hz, huz⟩
  have hzE : (z : E) ∈ Submodule.span K
      (Set.range (fun i => (x i : E))) := by
    refine Submodule.span_induction (s := Set.range x)
      (p := fun (z : {z : E // z ∈ V}) _ =>
      (z : E) ∈ Submodule.span K
        (Set.range (fun i => (x i : E)))) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      exact Submodule.add_mem _ ha hb
    · intro c a _ ha
      exact Submodule.smul_mem _ c ha
  have huz' : (u : E) + (z : E) = y := congrArg Subtype.val huz
  have huE : (u : E) ∈ U := Submodule.mem_comap.mp hu
  have huW : (u : E) ∈ W := (show U ≤ W from le_sup_left) huE
  have hzW : (z : E) ∈ W :=
    (show Submodule.span K (Set.range (fun i => (x i : E))) ≤ W from
      le_sup_right) hzE
  rw [← huz']
  exact W.add_mem huW hzW

end Katznelson
