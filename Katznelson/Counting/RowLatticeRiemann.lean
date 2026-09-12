import Katznelson.Counting.RowLattice
import Katznelson.Counting.SubspaceRiemann
import Katznelson.Counting.ControlledVoronoi
import Mathlib.Analysis.InnerProductSpace.OfNorm

/-!
# Riemann sums for matrices with rows in a lattice

This file specializes Lemma `le:Riemann_estimate` to the lattice
`M_n(Λ_D)` from Definition `de:defi_of_M_t` and rewrites its lattice sum as
the sum over integral matrices used in Lemma `le:without_rank_cond`.
-/

namespace Katznelson

open MeasureTheory Set Module
open scoped Classical MeasureTheory NumberField

section

variable {K : Type*} [Field K] [NumberField K]

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   The projected ambient row module inherits the ambient covering radius,
   because orthogonal projection is norm non-increasing. -/
set_option maxHeartbeats 800000 in
theorem projectedAmbientRowModule_isLatticeCovering_of_ambient
    {m l : ℕ} (V : Grassmannian K m l) {R : ℝ}
    (hcover : LatticeCovering (ambientIntegralRowModule (K := K) m) R) :
    LatticeCovering (projectedAmbientRowModule (K := K) V) R := by
  simpa [projectedAmbientRowModule, projectedAmbientRowMap] using
    (latticeCovering_orthogonalProjection
      (U := (rowRealSpan V)ᗮ)
      (L := ambientIntegralRowModule (K := K) m) hcover)

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1479]
   The radius is the intrinsic covering radius of the ambient row lattice,
   hence it is independent of the lower-rank space `V`. -/
theorem projectedAmbientRowModule_isLatticeCovering_of_ambientRadius
    {m l : ℕ} (V : Grassmannian K m l) :
    LatticeCovering (projectedAmbientRowModule (K := K) V)
      (latticeCoveringRadius (ambientIntegralRowModule (K := K) m)) := by
  exact projectedAmbientRowModule_isLatticeCovering_of_ambient V
    (latticeCovering_latticeCoveringRadius
      (ambientIntegralRowModule (K := K) m))

/- [Lean infrastructure] Package topology-sensitive quantities behind
   definitions.  Matrix norms are scoped in Mathlib, so exposing their
   instances in theorem signatures would create instance diamonds. -/
noncomputable def rowMatrixFundamentalRadius
    {m k : ℕ} (V : Grassmannian K m k) (n : ℕ) : ℝ :=
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) := inferInstance
  let hZ := @IsZLattice.mk ℝ inferInstance (rowMatrixRealSpan V n)
    inferInstance inferInstance (rowMatrixZLattice V n) hdisc
    (rowMatrixZLattice_span_top V n)
  @latticeFundamentalRadius (rowMatrixRealSpan V n) inferInstance inferInstance
    inferInstance (rowMatrixZLattice V n) hdisc hZ

/- [derived consequence, paper `le:without_rank_cond`, lines 1038--1044]
   The intrinsic Voronoi-radius interface for the matrix lattice.  This is
   kept separate from `rowMatrixFundamentalRadius`, which is the arbitrary
   basis radius used by the current cell decomposition in `RiemannSum`. -/
theorem rowMatrixZLattice_isLatticeCovering_intrinsic
    {m k n : ℕ} (V : Grassmannian K m k) :
    LatticeCovering (rowMatrixZLattice V n)
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) := by
  apply rowMatrixZLattice_isLatticeCovering_of_isLatticeCovering V
    (latticeCoveringRadius_nonneg (rowZLattice V))
  exact latticeCovering_latticeCoveringRadius (rowZLattice V)

noncomputable def rowMatrixLatticeCovolume
    {m k : ℕ} (V : Grassmannian K m k) (n : ℕ) : ℝ :=
  @ZLattice.covolume (rowMatrixRealSpan V n) inferInstance
    (@Subtype.instMeasurableSpace (M n m (K_ℝ[K]))
      (fun x => x ∈ rowMatrixRealSpan V n)
      (kRealMatrixMeasurableSpace (K := K)))
    (rowMatrixZLattice V n) (rowMatrixEuclideanMeasure (n := n) V)

theorem rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow
    {m k n : ℕ} (V : Grassmannian K m k) :
    rowMatrixLatticeCovolume V n = (rowSpaceHeight V) ^ n := by
  simpa [rowMatrixLatticeCovolume] using
    (rowMatrixZLattice_covolume_eq_rowSpaceHeight_pow V)

noncomputable def rowMatrixSubspaceIntegral
    {m k : ℕ} (V : Grassmannian K m k) (n : ℕ)
    (f : M n m (K_ℝ[K]) → ℝ) : ℝ :=
  let msX : MeasurableSpace (M n m (K_ℝ[K])) := borel _
  let bsX : @BorelSpace (M n m (K_ℝ[K])) inferInstance msX := ⟨rfl⟩
  let msW : MeasurableSpace (rowMatrixRealSpan V n) :=
    @Subtype.instMeasurableSpace (M n m (K_ℝ[K]))
      (fun x => x ∈ rowMatrixRealSpan V n) msX
  let bsW : @BorelSpace (rowMatrixRealSpan V n) inferInstance msW :=
    @Subtype.borelSpace (M n m (K_ℝ[K])) inferInstance msX bsX
      (fun x => x ∈ rowMatrixRealSpan V n)
  let mu : @Measure (rowMatrixRealSpan V n) msW :=
    @Measure.euclideanHausdorffMeasure (rowMatrixRealSpan V n)
      inferInstance msW bsW (Module.finrank ℝ (rowMatrixRealSpan V n))
  @MeasureTheory.integral (rowMatrixRealSpan V n) ℝ inferInstance
    inferInstance msW mu (fun x => f x)

theorem rowMatrixFundamentalRadius_nonneg
    {m k n : ℕ} (V : Grassmannian K m k) :
    0 ≤ rowMatrixFundamentalRadius V n := by
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) :=
    rowMatrixZLattice.discreteTopology (n := n) V
  let hZ : @IsZLattice ℝ inferInstance (rowMatrixRealSpan V n)
      inferInstance inferInstance (rowMatrixZLattice V n) hdisc :=
    @IsZLattice.mk ℝ inferInstance (rowMatrixRealSpan V n)
      inferInstance inferInstance (rowMatrixZLattice V n) hdisc
      (rowMatrixZLattice_span_top V n)
  change 0 ≤ @latticeFundamentalRadius (rowMatrixRealSpan V n)
    inferInstance inferInstance inferInstance (rowMatrixZLattice V n) hdisc hZ
  exact @latticeFundamentalRadius_nonneg (rowMatrixRealSpan V n)
    inferInstance inferInstance inferInstance (rowMatrixZLattice V n) hdisc hZ

theorem rowMatrixFundamentalRadius_pos
    {m k n : ℕ} (V : Grassmannian K m k)
    (hk : 0 < k) (hn : 0 < n) :
    0 < rowMatrixFundamentalRadius V n := by
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) :=
    rowMatrixZLattice.discreteTopology (n := n) V
  let hZ : @IsZLattice ℝ inferInstance (rowMatrixRealSpan V n)
      inferInstance inferInstance (rowMatrixZLattice V n) hdisc :=
    @IsZLattice.mk ℝ inferInstance (rowMatrixRealSpan V n)
      inferInstance inferInstance (rowMatrixZLattice V n) hdisc
      (rowMatrixZLattice_span_top V n)
  letI : Nontrivial (rowMatrixRealSpan V n) :=
    Submodule.nontrivial_iff_ne_bot.mpr
      (rowMatrixRealSpan_ne_bot_of_pos V hk hn)
  change 0 < @latticeFundamentalRadius (rowMatrixRealSpan V n)
    inferInstance inferInstance inferInstance (rowMatrixZLattice V n) hdisc hZ
  exact @latticeFundamentalRadius_pos (rowMatrixRealSpan V n)
    inferInstance inferInstance inferInstance (rowMatrixZLattice V n) hdisc hZ
    inferInstance

theorem rowMatrixLatticeCovolume_pos
    {m k n : ℕ} (V : Grassmannian K m k) :
    0 < rowMatrixLatticeCovolume V n := by
  rw [rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow V]
  exact pow_pos (rowSpaceHeight_pos V) n

/- [derived consequence, paper `le:ballvol`, lines 463--478]
   Specialize the general lattice-point estimate to `M_n(Λ_D)`.  The
   Euclidean Hausdorff measure is written with the same explicit subtype
   measurable space as the covolume definition, so the specialization keeps
   the manuscript's height normalization available for the later inner-sum
   estimate. -/
set_option maxHeartbeats 5000000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem rowMatrix_lattice_ball_count
    {m k n : ℕ} (V : Grassmannian K m k) {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧
      (Set.ncard {A : rowMatrixZLattice V n |
          ‖(A : rowMatrixRealSpan V n)‖ ≤ T} : ℝ) ≤
        C * (T + rowMatrixFundamentalRadius V n) ^
            Module.finrank ℝ (rowMatrixRealSpan V n) *
          (rowMatrixLatticeCovolume V n)⁻¹ := by
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
  letI : NormedAddCommGroup (rowMatrixRealSpan V n) := nsgW
  letI : NormedSpace ℝ (rowMatrixRealSpan V n) := nspW
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) :=
    rowMatrixZLattice.discreteTopology (n := n) V
  letI : DiscreteTopology (rowMatrixZLattice V n) := hdisc
  let hZ := @IsZLattice.mk ℝ inferInstance (rowMatrixRealSpan V n)
    inferInstance inferInstance (rowMatrixZLattice V n) hdisc
    (rowMatrixZLattice_span_top V n)
  let mu : @Measure (rowMatrixRealSpan V n) msW :=
    @Measure.euclideanHausdorffMeasure (rowMatrixRealSpan V n)
      inferInstance msW bsW (Module.finrank ℝ (rowMatrixRealSpan V n))
  let hhaar : mu.IsAddHaarMeasure := by
    dsimp [mu]
    exact @MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure
      (rowMatrixRealSpan V n) nsgW nspW fdW msW bsW
  letI : mu.IsAddHaarMeasure := hhaar
  obtain ⟨C, hC, hball⟩ :=
    @lattice_ball_count (rowMatrixRealSpan V n) nsgW nspW fdW
      (rowMatrixZLattice V n) hdisc hZ msW bsW inferInstance mu hhaar T hT
  refine ⟨C, hC, ?_⟩
  simpa only [mu, rowMatrixFundamentalRadius, rowMatrixLatticeCovolume,
    rowMatrixEuclideanMeasure] using hball

/- The same estimate in the manuscript's height normalization. -/
theorem rowMatrix_lattice_ball_count_height
    {m k n : ℕ} (V : Grassmannian K m k) {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧
      (Set.ncard {A : rowMatrixZLattice V n |
          ‖(A : rowMatrixRealSpan V n)‖ ≤ T} : ℝ) ≤
        C * (T + rowMatrixFundamentalRadius V n) ^
            (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n := by
  obtain ⟨C, hC, hball⟩ := rowMatrix_lattice_ball_count (n := n) V hT
  refine ⟨C, hC, ?_⟩
  rw [rowMatrixRealSpan_finrank V,
    rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow,
    ← inv_pow] at hball
  exact hball

/- [derived consequence, paper `le:ballvol`, lines 463--478]
   Uniform version of the matrix-lattice ball count.  The paper's exponent,
   fundamental-radius term, and height factor are unchanged.  The explicit
   Euclidean unit-ball volume is Lean infrastructure that records why the
   implicit coefficient is independent of the varying row space `V`. -/
set_option maxHeartbeats 1200000 in
theorem rowMatrix_lattice_ball_count_height_uniform
    {m k n : ℕ} (V : Grassmannian K m k)
    (hk : 0 < k) (hn : 0 < n) {T : ℝ} (hT : 0 < T) :
    (Set.ncard {A : rowMatrixZLattice V n |
        ‖(A : rowMatrixRealSpan V n)‖ ≤ T} : ℝ) ≤
      euclideanUnitBallVolume (n * (k * degree K)) *
        (T + rowMatrixFundamentalRadius V n) ^
            (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n := by
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
  let properW : ProperSpace (rowMatrixRealSpan V n) := inferInstance
  letI : NormedAddCommGroup (rowMatrixRealSpan V n) := nsgW
  letI : NormedSpace ℝ (rowMatrixRealSpan V n) := nspW
  letI : NormedSpace ℝ (rowRealSpan V) :=
    Submodule.normedSpace (rowRealSpan V)
  letI : InnerProductSpace ℝ (rowRealSpan V) :=
    Submodule.innerProductSpace (rowRealSpan V)
  letI : NormedSpace ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V)) :=
    PiLp.normedSpace (p := 2) ℝ _
  letI : InnerProductSpace ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V)) :=
    PiLp.innerProductSpace _
  let ipsW : InnerProductSpace ℝ (rowMatrixRealSpan V n) :=
    InnerProductSpace.ofNorm ℝ (by
      intro x y
      let e := rowMatrixRealSpanLpIsometryEquiv (n := n) V
      have h := parallelogram_law_with_norm_mul ℝ (e x) (e y)
      simpa only [← e.map_add, ← e.map_sub, e.norm_map] using h)
  letI : InnerProductSpace ℝ (rowMatrixRealSpan V n) := ipsW
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) :=
    rowMatrixZLattice.discreteTopology (n := n) V
  letI : DiscreteTopology (rowMatrixZLattice V n) := hdisc
  let hZ := @IsZLattice.mk ℝ inferInstance (rowMatrixRealSpan V n)
    inferInstance inferInstance (rowMatrixZLattice V n) hdisc
    (rowMatrixZLattice_span_top V n)
  let mu : @Measure (rowMatrixRealSpan V n) msW :=
    @Measure.euclideanHausdorffMeasure (rowMatrixRealSpan V n)
      inferInstance msW bsW (Module.finrank ℝ (rowMatrixRealSpan V n))
  let hhaar : mu.IsAddHaarMeasure := by
    dsimp [mu]
    exact @MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure
      (rowMatrixRealSpan V n) nsgW nspW fdW msW bsW
  letI : mu.IsAddHaarMeasure := hhaar
  have hdim : Module.finrank ℝ (rowMatrixRealSpan V n) =
      n * (k * degree K) := rowMatrixRealSpan_finrank V
  have hqpos : 0 < Module.finrank ℝ (rowMatrixRealSpan V n) := by
    rw [hdim]
    exact Nat.mul_pos hn (Nat.mul_pos hk Module.finrank_pos)
  let hnontriv : Nontrivial (rowMatrixRealSpan V n) :=
    Module.nontrivial_of_finrank_pos hqpos
  letI : Nontrivial (rowMatrixRealSpan V n) := hnontriv
  have hunit : mu.real (Metric.closedBall (0 : rowMatrixRealSpan V n) 1) =
      euclideanUnitBallVolume (n * (k * degree K)) := by
    simpa [mu, hdim] using
      (@euclideanHausdorffMeasureReal_unitClosedBall
        (rowMatrixRealSpan V n) nsgW ipsW fdW msW bsW hnontriv)
  have hcover : LatticeCovering (rowMatrixZLattice V n)
      (rowMatrixFundamentalRadius V n) := by
    change LatticeCovering (rowMatrixZLattice V n)
      (@latticeFundamentalRadius (rowMatrixRealSpan V n) nsgW nspW fdW
        (rowMatrixZLattice V n) hdisc hZ)
    intro x
    obtain ⟨v, hv⟩ :=
      (@latticeCovering_latticeCoveringRadius
        (rowMatrixRealSpan V n) nsgW nspW fdW
        (rowMatrixZLattice V n) hdisc hZ) x
    exact ⟨v, hv.trans
      (@latticeCoveringRadius_le_latticeFundamentalRadius
        (rowMatrixRealSpan V n) nsgW nspW fdW
        (rowMatrixZLattice V n) hdisc hZ)⟩
  have hcount :=
    @lattice_ball_count_of_latticeCovering_unitBall
      (rowMatrixRealSpan V n) nsgW ipsW fdW properW msW bsW
      (rowMatrixZLattice V n) hdisc hZ mu hhaar T
      (rowMatrixFundamentalRadius V n) hT hcover
  have hcov : (ZLattice.covolume (rowMatrixZLattice V n) mu)⁻¹ =
      (rowSpaceHeight V)⁻¹ ^ n := by
    have hcovbase : ZLattice.covolume (rowMatrixZLattice V n) mu =
        (rowSpaceHeight V) ^ n := by
      simpa [mu, rowMatrixEuclideanMeasure] using
        (rowMatrixZLattice_covolume_eq_rowSpaceHeight_pow V)
    calc
      (ZLattice.covolume (rowMatrixZLattice V n) mu)⁻¹ =
          ((rowSpaceHeight V) ^ n)⁻¹ :=
        congrArg (fun x : ℝ => x⁻¹) hcovbase
      _ = (rowSpaceHeight V)⁻¹ ^ n := by rw [inv_pow]
  calc
    (Set.ncard {A : rowMatrixZLattice V n |
        ‖(A : rowMatrixRealSpan V n)‖ ≤ T} : ℝ) ≤
        mu.real (Metric.closedBall (0 : rowMatrixRealSpan V n) 1) *
          (T + rowMatrixFundamentalRadius V n) ^
            Module.finrank ℝ (rowMatrixRealSpan V n) *
          (ZLattice.covolume (rowMatrixZLattice V n) mu)⁻¹ := hcount
    _ = euclideanUnitBallVolume (n * (k * degree K)) *
          (T + rowMatrixFundamentalRadius V n) ^
            (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n := by
      rw [hunit, hdim, hcov]

/- [derived consequence, paper `le:ballvol`, lines 463--478] The same
   uniform ball-count estimate with an arbitrary lattice-covering witness.
   This is the form needed to retain the manuscript's intrinsic radius `ρ`:
   the preceding fundamental-radius theorem is only one specialization of
   this argument. -/
set_option maxHeartbeats 1200000 in
theorem rowMatrix_lattice_ball_count_height_uniform_of_latticeCovering
    {m k n : ℕ} (V : Grassmannian K m k)
    (hk : 0 < k) (hn : 0 < n) {T R : ℝ} (hT : 0 < T)
    (hcover : LatticeCovering (rowMatrixZLattice V n) R) :
    (Set.ncard {A : rowMatrixZLattice V n |
        ‖(A : rowMatrixRealSpan V n)‖ ≤ T} : ℝ) ≤
      euclideanUnitBallVolume (n * (k * degree K)) *
        (T + R) ^ (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n := by
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
  let properW : ProperSpace (rowMatrixRealSpan V n) := inferInstance
  letI : NormedAddCommGroup (rowMatrixRealSpan V n) := nsgW
  letI : NormedSpace ℝ (rowMatrixRealSpan V n) := nspW
  letI : NormedSpace ℝ (rowRealSpan V) :=
    Submodule.normedSpace (rowRealSpan V)
  letI : InnerProductSpace ℝ (rowRealSpan V) :=
    Submodule.innerProductSpace (rowRealSpan V)
  letI : NormedSpace ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V)) :=
    PiLp.normedSpace (p := 2) ℝ _
  letI : InnerProductSpace ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V)) :=
    PiLp.innerProductSpace _
  let ipsW : InnerProductSpace ℝ (rowMatrixRealSpan V n) :=
    InnerProductSpace.ofNorm ℝ (by
      intro x y
      let e := rowMatrixRealSpanLpIsometryEquiv (n := n) V
      have h := parallelogram_law_with_norm_mul ℝ (e x) (e y)
      simpa only [← e.map_add, ← e.map_sub, e.norm_map] using h)
  letI : InnerProductSpace ℝ (rowMatrixRealSpan V n) := ipsW
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) :=
    rowMatrixZLattice.discreteTopology (n := n) V
  letI : DiscreteTopology (rowMatrixZLattice V n) := hdisc
  let hZ := @IsZLattice.mk ℝ inferInstance (rowMatrixRealSpan V n)
    inferInstance inferInstance (rowMatrixZLattice V n) hdisc
    (rowMatrixZLattice_span_top V n)
  let mu : @Measure (rowMatrixRealSpan V n) msW :=
    @Measure.euclideanHausdorffMeasure (rowMatrixRealSpan V n)
      inferInstance msW bsW (Module.finrank ℝ (rowMatrixRealSpan V n))
  let hhaar : mu.IsAddHaarMeasure := by
    dsimp [mu]
    exact @MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure
      (rowMatrixRealSpan V n) nsgW nspW fdW msW bsW
  letI : mu.IsAddHaarMeasure := hhaar
  have hdim : Module.finrank ℝ (rowMatrixRealSpan V n) =
      n * (k * degree K) := rowMatrixRealSpan_finrank V
  have hqpos : 0 < Module.finrank ℝ (rowMatrixRealSpan V n) := by
    rw [hdim]
    exact Nat.mul_pos hn (Nat.mul_pos hk Module.finrank_pos)
  let hnontriv : Nontrivial (rowMatrixRealSpan V n) :=
    Module.nontrivial_of_finrank_pos hqpos
  letI : Nontrivial (rowMatrixRealSpan V n) := hnontriv
  have hunit : mu.real (Metric.closedBall (0 : rowMatrixRealSpan V n) 1) =
      euclideanUnitBallVolume (n * (k * degree K)) := by
    simpa [mu, hdim] using
      (@euclideanHausdorffMeasureReal_unitClosedBall
        (rowMatrixRealSpan V n) nsgW ipsW fdW msW bsW hnontriv)
  have hcount :=
    @lattice_ball_count_of_latticeCovering_unitBall
      (rowMatrixRealSpan V n) nsgW ipsW fdW properW msW bsW
      (rowMatrixZLattice V n) hdisc hZ mu hhaar T R hT hcover
  have hcov : (ZLattice.covolume (rowMatrixZLattice V n) mu)⁻¹ =
      (rowSpaceHeight V)⁻¹ ^ n := by
    have hcovbase : ZLattice.covolume (rowMatrixZLattice V n) mu =
        (rowSpaceHeight V) ^ n := by
      simpa [mu, rowMatrixEuclideanMeasure] using
        (rowMatrixZLattice_covolume_eq_rowSpaceHeight_pow V)
    calc
      (ZLattice.covolume (rowMatrixZLattice V n) mu)⁻¹ =
          ((rowSpaceHeight V) ^ n)⁻¹ :=
        congrArg (fun x : ℝ => x⁻¹) hcovbase
      _ = (rowSpaceHeight V)⁻¹ ^ n := by rw [inv_pow]
  calc
    (Set.ncard {A : rowMatrixZLattice V n |
        ‖(A : rowMatrixRealSpan V n)‖ ≤ T} : ℝ) ≤
        mu.real (Metric.closedBall (0 : rowMatrixRealSpan V n) 1) *
          (T + R) ^ Module.finrank ℝ (rowMatrixRealSpan V n) *
          (ZLattice.covolume (rowMatrixZLattice V n) mu)⁻¹ := hcount
    _ = euclideanUnitBallVolume (n * (k * degree K)) *
          (T + R) ^ (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n := by
      rw [hunit, hdim, hcov]

/- [derived consequence, paper `le:ballvol`, lines 463--478] Specialize the
   preceding ball count to the intrinsic covering radius of `M_n(Λ_D)`.
   The factor `sqrt n` is retained exactly as in `le:without_rank_cond`. -/
theorem rowMatrix_lattice_ball_count_height_uniform_intrinsic
    {m k n : ℕ} (V : Grassmannian K m k)
    (hk : 0 < k) (hn : 0 < n) {T : ℝ} (hT : 0 < T) :
    (Set.ncard {A : rowMatrixZLattice V n |
        ‖(A : rowMatrixRealSpan V n)‖ ≤ T} : ℝ) ≤
      euclideanUnitBallVolume (n * (k * degree K)) *
        (T + Real.sqrt (n : ℝ) *
          latticeCoveringRadius (rowZLattice V)) ^
            (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n := by
  exact rowMatrix_lattice_ball_count_height_uniform_of_latticeCovering
    V hk hn hT (rowMatrixZLattice_isLatticeCovering_intrinsic V)

/- The support and boundedness interfaces used in the paper's lower-rank
   estimate.  They are stated separately so the row-matrix specialization
   does not hide these hypotheses inside a large elaboration. -/
theorem Admissible.rowMatrix_abs_compactSupport
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f) :
    HasCompactSupport
      (fun x : rowMatrixRealSpan V n => |f (x : M n m (K_ℝ[K]))|) := by
  let K₀ : Set (rowMatrixRealSpan V n) :=
    (Subtype.val : rowMatrixRealSpan V n → M n m (K_ℝ[K])) ⁻¹' tsupport f
  have hK₀ : IsCompact K₀ := by
    dsimp [K₀]
    exact (rowMatrixRealSpan V n).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isCompact_preimage
      h_f.compactSupport
  have hK₀closed : IsClosed K₀ := by
    dsimp [K₀]
    exact (isClosed_tsupport f).preimage continuous_subtype_val
  refine IsCompact.of_isClosed_subset hK₀ (isClosed_tsupport _) ?_
  apply closure_minimal _ hK₀closed
  intro x hx
  change (x : M n m (K_ℝ[K])) ∈ tsupport f
  exact subset_closure (abs_ne_zero.mp hx)

theorem Admissible.rowMatrix_scaled_abs_support_bound
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ A : rowMatrixZLattice V n,
      |f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))| ≠ 0 →
        ‖(A : rowMatrixRealSpan V n)‖ ≤ (R + 1) * T := by
  obtain ⟨R, hR, hRsupport⟩ := h_f.exists_support_radius
  refine ⟨R, hR, ?_⟩
  intro A hA
  have hfnonzero : f (T⁻¹ • (((A : rowMatrixRealSpan V n) :
      M n m (K_ℝ[K])))) ≠ 0 := by
    exact abs_ne_zero.mp hA
  have hball := hRsupport _ hfnonzero
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hT] at hball
  calc
    ‖(A : rowMatrixRealSpan V n)‖ =
        T * (T⁻¹ * ‖(A : rowMatrixRealSpan V n)‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]
    _ ≤ T * R := mul_le_mul_of_nonneg_left hball hT.le
    _ ≤ T * (R + 1) := mul_le_mul_of_nonneg_left (by linarith) hT.le
    _ = (R + 1) * T := by ring

theorem Admissible.rowMatrix_scaled_abs_bound
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f) {T : ℝ} :
    ∃ C : ℝ, 0 < C ∧ ∀ A : rowMatrixZLattice V n,
      |(|f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))|)| ≤ C := by
  obtain ⟨C₀, hC₀, hbound⟩ := h_f.exists_uniform_bound
  refine ⟨C₀ + 1, by linarith, ?_⟩
  intro A
  rw [abs_abs]
  exact (hbound _).trans (by linarith)

theorem lattice_ball_count_scaled_of_radius
    {N C R T C_R r H : ℝ} {q : ℕ}
    (hT : 0 < T) (hC : 0 ≤ C) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hC_R : 0 ≤ C_R) (hr : 0 ≤ r) (hRadius : r / T ≤ C_R)
    (hcount : N ≤ C * ((R + 1) * T + r) ^ q * H) :
    N ≤ C * (R + 1 + C_R) ^ q * H * T ^ q := by
  have hr' : r ≤ C_R * T := (div_le_iff₀ hT).mp hRadius
  have hsum : (R + 1) * T + r ≤ (R + 1 + C_R) * T := by
    calc
      (R + 1) * T + r ≤ (R + 1) * T + C_R * T :=
        add_le_add (le_refl _) hr'
      _ = (R + 1 + C_R) * T := by ring
  have hpow :
      ((R + 1) * T + r) ^ q ≤ ((R + 1 + C_R) * T) ^ q := by
    apply pow_le_pow_left₀
    · exact add_nonneg (mul_nonneg (by linarith) hT.le) hr
    · exact hsum
  calc
    N ≤ C * ((R + 1 + C_R) * T) ^ q * H := by
      exact hcount.trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hC) hH)
    _ = C * (R + 1 + C_R) ^ q * H * T ^ q := by
      rw [mul_pow]
      ac_rfl

/-
set_option maxHeartbeats 5000000 in
theorem rowMatrix_lattice_ball_count_height_scaled
    {m k n : ℕ} (V : Grassmannian K m k) {T C_R R : ℝ}
    (hT : 0 < T) (hC_R : 0 ≤ C_R) (hRadius :
      rowMatrixFundamentalRadius V n / T ≤ C_R) (hR : 0 ≤ R) :
    ∃ Cball : ℝ, 0 < Cball ∧
      (Set.ncard {A : rowMatrixZLattice V n |
        ‖(A : rowMatrixRealSpan V n)‖ ≤ (R + 1) * T} : ℝ) ≤
        Cball * (R + 1 + C_R) ^ (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)) := by
  exact rowMatrix_lattice_ball_count_height_scaled_proved V hT hC_R hRadius hR
/-
  let B : ℝ := (R + 1) * T
  have hB : 0 < B := by
    dsimp [B]
    exact mul_pos (by linarith) hT
  obtain ⟨Cball, hCball, hball⟩ :=
    rowMatrix_lattice_ball_count_height (n := n) V hB
  have hRad' : rowMatrixFundamentalRadius V n ≤ C_R * T :=
    (div_le_iff₀ hT).mp hRadius
  have hsum_radius : B + rowMatrixFundamentalRadius V n ≤
      (R + 1 + C_R) * T := by
    dsimp [B]
    calc
      (R + 1) * T + rowMatrixFundamentalRadius V n ≤
          (R + 1) * T + C_R * T := add_le_add (le_refl _) hRad'
      _ = (R + 1 + C_R) * T := by ring
  have hpow_radius :
      (B + rowMatrixFundamentalRadius V n) ^ (n * (k * degree K)) ≤
        ((R + 1 + C_R) * T) ^ (n * (k * degree K)) := by
    apply pow_le_pow_left₀
    · exact add_nonneg (le_of_lt (by
        exact mul_pos (by linarith) hT))
        (rowMatrixFundamentalRadius_nonneg V)
    · exact hsum_radius
  refine ⟨Cball, hCball, ?_⟩
  calc
    (Set.ncard {A : rowMatrixZLattice V n |
        ‖(A : rowMatrixRealSpan V n)‖ ≤ (R + 1) * T} : ℝ) ≤
        Cball * (B + rowMatrixFundamentalRadius V n) ^
            (n * (k * degree K)) * (rowSpaceHeight V)⁻¹ ^ n := by
      dsimp [B] at hball
      exact hball
    _ ≤ Cball * ((R + 1 + C_R) * T) ^ (n * (k * degree K)) *
        (rowSpaceHeight V)⁻¹ ^ n := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow_radius hCball.le) (by positivity)
    _ = Cball * (R + 1 + C_R) ^ (n * (k * degree K)) *
        (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)) := by
      rw [mul_pow]
      ring
-/
-/

set_option maxHeartbeats 1000000 in
theorem rowMatrix_lattice_ball_count_height_scaled
    {m k n : ℕ} (V : Grassmannian K m k) {T C_R R : ℝ}
    (hT : 0 < T) (hC_R : 0 ≤ C_R) (hRadius :
      rowMatrixFundamentalRadius V n / T ≤ C_R) (hR : 0 ≤ R) :
    ∃ Cball : ℝ, 0 < Cball ∧
      (Set.ncard {A : rowMatrixZLattice V n |
        ‖(A : rowMatrixRealSpan V n)‖ ≤ (R + 1) * T} : ℝ) ≤
        Cball * (R + 1 + C_R) ^ (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)) := by
  have hB : 0 < (R + 1) * T := mul_pos (by linarith) hT
  obtain ⟨Cball, hCball, hball⟩ :=
    rowMatrix_lattice_ball_count_height (n := n) V hB
  refine ⟨Cball, hCball, ?_⟩
  have hH : 0 ≤ (rowSpaceHeight V)⁻¹ ^ n :=
    pow_nonneg (inv_nonneg.mpr (rowSpaceHeight_pos V).le) n
  exact lattice_ball_count_scaled_of_radius
    (N := (Set.ncard {A : rowMatrixZLattice V n |
      ‖(A : rowMatrixRealSpan V n)‖ ≤ (R + 1) * T} : ℝ))
    (C := Cball) (R := R) (T := T) (C_R := C_R)
    (r := rowMatrixFundamentalRadius V n)
    (H := (rowSpaceHeight V)⁻¹ ^ n)
    (q := n * (k * degree K)) hT hCball.le hH hR hC_R
    (rowMatrixFundamentalRadius_nonneg V) hRadius hball

/- [derived consequence, paper `le:low_rank_terms`, lines 1558--1568]
   Scaled uniform form of the preceding ball count.  This is exactly the
   paper's support-radius comparison, with the dimension-only unit-ball
   coefficient retained so it cannot vary with `V` or `T`. -/
set_option maxHeartbeats 1200000 in
theorem rowMatrix_lattice_ball_count_height_scaled_uniform
    {m k n : ℕ} (V : Grassmannian K m k)
    (hk : 0 < k) (hn : 0 < n) {T C_R R : ℝ}
    (hT : 0 < T) (hC_R : 0 ≤ C_R) (hRadius :
      rowMatrixFundamentalRadius V n / T ≤ C_R) (hR : 0 ≤ R) :
    (Set.ncard {A : rowMatrixZLattice V n |
      ‖(A : rowMatrixRealSpan V n)‖ ≤ (R + 1) * T} : ℝ) ≤
        euclideanUnitBallVolume (n * (k * degree K)) *
          (R + 1 + C_R) ^ (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)) := by
  have hB : 0 < (R + 1) * T := mul_pos (by linarith) hT
  have hball := rowMatrix_lattice_ball_count_height_uniform V hk hn hB
  have hH : 0 ≤ (rowSpaceHeight V)⁻¹ ^ n :=
    pow_nonneg (inv_nonneg.mpr (rowSpaceHeight_pos V).le) n
  exact lattice_ball_count_scaled_of_radius
    (N := (Set.ncard {A : rowMatrixZLattice V n |
      ‖(A : rowMatrixRealSpan V n)‖ ≤ (R + 1) * T} : ℝ))
    (C := euclideanUnitBallVolume (n * (k * degree K)))
    (R := R) (T := T) (C_R := C_R)
    (r := rowMatrixFundamentalRadius V n)
    (H := (rowSpaceHeight V)⁻¹ ^ n)
    (q := n * (k * degree K)) hT (euclideanUnitBallVolume_pos _).le hH hR
    hC_R (rowMatrixFundamentalRadius_nonneg V) hRadius hball

/- [derived consequence, paper `le:ballvol`, lines 463--478] Scaled version
   of the intrinsic-radius ball count.  This is the exact support-radius
   input needed in the lower-rank argument, with `sqrt n * rho(Λ_D)` rather
   than the auxiliary fundamental-parallelepiped radius. -/
set_option maxHeartbeats 1200000 in
theorem rowMatrix_lattice_ball_count_height_scaled_uniform_intrinsic
    {m k n : ℕ} (V : Grassmannian K m k)
    (hk : 0 < k) (hn : 0 < n) {T C_R R : ℝ}
    (hT : 0 < T) (hC_R : 0 ≤ C_R)
    (hRadius :
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) / T ≤ C_R)
    (hR : 0 ≤ R) :
    (Set.ncard {A : rowMatrixZLattice V n |
      ‖(A : rowMatrixRealSpan V n)‖ ≤ (R + 1) * T} : ℝ) ≤
        euclideanUnitBallVolume (n * (k * degree K)) *
          (R + 1 + C_R) ^ (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)) := by
  have hB : 0 < (R + 1) * T := mul_pos (by linarith) hT
  have hball := rowMatrix_lattice_ball_count_height_uniform_intrinsic
    V hk hn hB
  have hH : 0 ≤ (rowSpaceHeight V)⁻¹ ^ n :=
    pow_nonneg (inv_nonneg.mpr (rowSpaceHeight_pos V).le) n
  have hr : 0 ≤ Real.sqrt (n : ℝ) *
      latticeCoveringRadius (rowZLattice V) :=
    mul_nonneg (Real.sqrt_nonneg _) (latticeCoveringRadius_nonneg _)
  exact lattice_ball_count_scaled_of_radius
    (N := (Set.ncard {A : rowMatrixZLattice V n |
      ‖(A : rowMatrixRealSpan V n)‖ ≤ (R + 1) * T} : ℝ))
    (C := euclideanUnitBallVolume (n * (k * degree K)))
    (R := R) (T := T) (C_R := C_R)
    (r := Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V))
    (H := (rowSpaceHeight V)⁻¹ ^ n)
    (q := n * (k * degree K)) hT (euclideanUnitBallVolume_pos _).le hH hR
    hC_R hr hRadius hball

/- [derived consequence, paper `le:low_rank_terms`, lines 1558--1568]
   The common finite-support step is separated from the row-matrix geometry.
   This is the paper's estimate after its lattice-point count has supplied
   the cardinality bound. -/
theorem lattice_subtype_scaled_sum_le_of_count
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ProperSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (P : L → Prop) (g : E → ℝ) (hcompact : HasCompactSupport g)
    (hg : ∀ x, 0 ≤ g x)
    {T B C D : ℝ} (hT : 0 < T)
    (hsupport : ∀ v : L, g (T⁻¹ • (v : E)) ≠ 0 → ‖(v : E)‖ ≤ B)
    (hbound : ∀ v : L, |g (T⁻¹ • (v : E))| ≤ C) (hC : 0 ≤ C)
    (hcount : (Set.ncard {v : L | ‖(v : E)‖ ≤ B} : ℝ) ≤ D) :
    ∑' v : {v : L // P v}, g (T⁻¹ • (v.1 : E)) ≤ C * D := by
  have hsum := lattice_subtype_scaled_sum_abs_le
    (L := L) P g hcompact hT hsupport hbound hC
  have hnonneg : 0 ≤
      ∑' v : {v : L // P v}, g (T⁻¹ • (v.1 : E)) :=
    tsum_nonneg (fun v => hg _)
  rw [abs_of_nonneg hnonneg] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left hcount hC)

/-
/- [derived consequence, paper `le:low_rank_terms`, lines 1558--1568]
   Bound the rank-`k` inner sum by the row-matrix ball count.  The radius
   hypothesis is kept explicit: the paper obtains it from the covering-radius
   corollary for the echelon family. -/
set_option maxHeartbeats 5000000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem Admissible.rowMatrix_rank_sum_abs_le_of_radius
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) {T C_R : ℝ}
    (hT : 1 ≤ T) (hC_R : 0 ≤ C_R)
    (hRadius : rowMatrixFundamentalRadius V n / T ≤ C_R) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      (∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
        |f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
          M n m (K_ℝ[K]))))|) ≤
        C₂ * (rowSpaceHeight V)⁻¹ ^ n *
          T ^ (n * (k * degree K)) := by
  exact rowMatrix_rank_sum_abs_le_of_radius_proved V h_f hk hn hT hC_R hRadius
/-
  have hcompact : HasCompactSupport
      (fun x : rowMatrixRealSpan V n => |f (x : M n m (K_ℝ[K]))|) := by
    let K₀ : Set (rowMatrixRealSpan V n) :=
      (Subtype.val : rowMatrixRealSpan V n → M n m (K_ℝ[K])) ⁻¹' tsupport f
    have hK₀ : IsCompact K₀ := by
      dsimp [K₀]
      exact (rowMatrixRealSpan V n).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal
        .isCompact_preimage h_f.compactSupport
    apply IsCompact.of_isClosed_subset hK₀ isClosed_tsupport
    apply closure_mono
    intro x hx
    change (x : M n m (K_ℝ[K])) ∈ tsupport f
    exact subset_closure hx
  obtain ⟨R, hR⟩ := h_f.compactSupport.isBounded.subset_closedBall
    (0 : M n m (K_ℝ[K]))
  let R₀ : ℝ := max R 0 + 1
  have hR₀ : 0 < R₀ := by
    dsimp [R₀]
    linarith [le_max_right R 0]
  have hR_support : ∀ {x : M n m (K_ℝ[K])}, x ∈ tsupport f → ‖x‖ ≤ R₀ := by
    intro x hx
    have hx' := hR hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx'
    exact hx'.trans (by
      dsimp [R₀]
      linarith [le_max_left R 0])
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  let B : ℝ := R₀ * T
  have hB : 0 < B := by
    dsimp [B]
    exact mul_pos hR₀ hT₀
  have hsupport : ∀ A : rowMatrixZLattice V n,
      |f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))| ≠ 0 →
        ‖(A : rowMatrixRealSpan V n)‖ ≤ B := by
    intro A hA
    have hfnonzero : f (T⁻¹ • (((A : rowMatrixRealSpan V n) :
        M n m (K_ℝ[K])))) ≠ 0 := by
      intro hzero
      apply hA
      simp [hzero]
    have hts : T⁻¹ • (((A : rowMatrixRealSpan V n) :
        M n m (K_ℝ[K]))) ∈ tsupport f :=
      subset_closure (show T⁻¹ • (((A : rowMatrixRealSpan V n) :
        M n m (K_ℝ[K]))) ∈ Function.support f from hfnonzero)
    have hball := hR_support hts
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hT₀] at hball
    dsimp [B]
    calc
      ‖(A : rowMatrixRealSpan V n)‖ =
          T * (T⁻¹ * ‖(A : rowMatrixRealSpan V n)‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hT₀.ne', one_mul]
      _ ≤ T * R₀ := mul_le_mul_of_nonneg_left hball hT₀.le
      _ = R₀ * T := by ring
  obtain ⟨C₀, hC₀⟩ := h_f.bounded.subset_closedBall (0 : ℝ)
  let C : ℝ := max C₀ 0 + 1
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbound : ∀ A : rowMatrixZLattice V n,
      |(|f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))|)| ≤ C := by
    intro A
    have hA := hC₀ ⟨f (T⁻¹ • (((A : rowMatrixRealSpan V n) :
        M n m (K_ℝ[K])))), rfl⟩
    rw [Metric.mem_closedBall, Real.dist_0_eq_abs] at hA
    rw [abs_abs]
    exact hA.trans (by
      dsimp [C]
      linarith [le_max_left C₀ 0])
  obtain ⟨Cball, hCball, hball⟩ := rowMatrix_lattice_ball_count_height V hB
  have hRad' : rowMatrixFundamentalRadius V n ≤ C_R * T :=
    (div_le_iff₀ hT₀).mp hRadius
  have hsum_radius : B + rowMatrixFundamentalRadius V n ≤ (R₀ + C_R) * T := by
    dsimp [B]
    calc
      R₀ * T + rowMatrixFundamentalRadius V n ≤ R₀ * T + C_R * T :=
        add_le_add_left hRad' _
      _ = (R₀ + C_R) * T := by ring
  have hpow_radius :
      (B + rowMatrixFundamentalRadius V n) ^ (n * (k * degree K)) ≤
        ((R₀ + C_R) * T) ^ (n * (k * degree K)) := by
    apply pow_le_pow_left₀
    · positivity
    · exact hsum_radius
  have hcount :
      (Set.ncard {A : rowMatrixZLattice V n |
        ‖(A : rowMatrixRealSpan V n)‖ ≤ B} : ℝ) ≤
        Cball * (R₀ + C_R) ^ (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)) := by
    calc
      (Set.ncard {A : rowMatrixZLattice V n |
          ‖(A : rowMatrixRealSpan V n)‖ ≤ B} : ℝ) ≤
          Cball * (B + rowMatrixFundamentalRadius V n) ^
              (n * (k * degree K)) * (rowSpaceHeight V)⁻¹ ^ n := hball
      _ ≤ Cball * ((R₀ + C_R) * T) ^ (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow_radius hCball.le) (by positivity)
      _ = Cball * (R₀ + C_R) ^ (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)) := by
        rw [mul_pow]
        ring
  let C₂ : ℝ := C * Cball * (R₀ + C_R) ^ (n * (k * degree K))
  have hC₂ : 0 < C₂ := by
    dsimp [C₂, C, R₀]
    have hdegree : 0 < degree K := Module.finrank_pos
    positivity
  refine ⟨C₂, hC₂, ?_⟩
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) :=
    rowMatrixZLattice.discreteTopology (n := n) V
  letI : DiscreteTopology (rowMatrixZLattice V n) := hdisc
  have hsum := lattice_subtype_scaled_sum_le_of_count
    (L := rowMatrixZLattice V n) (fun A => rowMatrixRank V A = k)
      (fun x : rowMatrixRealSpan V n => |f (x : M n m (K_ℝ[K]))|) hcompact
    (fun x => abs_nonneg _) hT₀ hsupport hbound hC hcount (by positivity)
  have hmain :
      (∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
        |f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))|) ≤
        C₂ * (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)) := by
    calc
      (∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
          |f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))|) ≤
          C * (Cball * (R₀ + C_R) ^ (n * (k * degree K)) *
            (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K))) := hsum
      _ = C₂ * (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)) := by
        dsimp [C₂]
        ring
  exact hmain
-/
-/

set_option maxHeartbeats 1000000 in
theorem Admissible.rowMatrix_rank_sum_abs_le_of_radius
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) {T C_R : ℝ}
    (hT : 1 ≤ T) (hC_R : 0 ≤ C_R)
    (hRadius : rowMatrixFundamentalRadius V n / T ≤ C_R) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      (∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
        |f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
          M n m (K_ℝ[K]))))|) ≤
        C₂ * (rowSpaceHeight V)⁻¹ ^ n *
          T ^ (n * (k * degree K)) := by
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) :=
    rowMatrixZLattice.discreteTopology (n := n) V
  letI : DiscreteTopology (rowMatrixZLattice V n) := hdisc
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  obtain ⟨R, hR, hsupport⟩ :=
    h_f.rowMatrix_scaled_abs_support_bound V hT₀
  obtain ⟨C, hC, hbound⟩ := h_f.rowMatrix_scaled_abs_bound V
  obtain ⟨Cball, hCball, hcount⟩ :=
    rowMatrix_lattice_ball_count_height_scaled V hT₀ hC_R hRadius hR
  let C₂ : ℝ := C * Cball * (R + 1 + C_R) ^ (n * (k * degree K))
  have hC₂ : 0 < C₂ := by
    dsimp [C₂]
    have hdegree : 0 < degree K := Module.finrank_pos
    have hbase : 0 < R + 1 + C_R := by linarith
    positivity
  refine ⟨C₂, hC₂, ?_⟩
  have hsum := @lattice_subtype_scaled_sum_le_of_count
    (rowMatrixRealSpan V n) inferInstance inferInstance inferInstance inferInstance
    (rowMatrixZLattice V n) hdisc inferInstance
      (fun A => rowMatrixRank V A = k)
      (fun x : rowMatrixRealSpan V n => |f (x : M n m (K_ℝ[K]))|)
      (h_f.rowMatrix_abs_compactSupport V) (fun x => abs_nonneg _)
      T ((R + 1) * T) C
      (Cball * (R + 1 + C_R) ^ (n * (k * degree K)) *
        (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)))
      hT₀ hsupport hbound hC.le hcount
  calc
    (∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
        |f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))|) ≤
        C * (Cball * (R + 1 + C_R) ^ (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K))) := hsum
    _ = C₂ * (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)) := by
      dsimp [C₂]
      ring

/- [derived consequence, paper `le:low_rank_terms`, lines 1558--1568]
   Fixed-coefficient form of the rank-`k` inner sum.  The supplied `R` and
   `C` are the global support and value bounds for the admissible function;
   making them inputs prevents a new coefficient from being chosen after the
   row space or scale has been fixed. -/
set_option maxHeartbeats 1200000 in
theorem Admissible.rowMatrix_rank_sum_abs_le_of_radius_uniform_of_bounds
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) {T C_R R C : ℝ}
    (hT : 1 ≤ T) (hC_R : 0 ≤ C_R)
    (hRadius : rowMatrixFundamentalRadius V n / T ≤ C_R)
    (hR : 0 ≤ R)
    (hsupport : ∀ A : rowMatrixZLattice V n,
      |f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))| ≠ 0 →
        ‖(A : rowMatrixRealSpan V n)‖ ≤ (R + 1) * T)
    (hC : 0 ≤ C)
    (hbound : ∀ A : rowMatrixZLattice V n,
      |(|f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))|)| ≤ C) :
    (∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
      |f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
        M n m (K_ℝ[K]))))|) ≤
      C * euclideanUnitBallVolume (n * (k * degree K)) *
        (R + 1 + C_R) ^ (n * (k * degree K)) *
        (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)) := by
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) :=
    rowMatrixZLattice.discreteTopology (n := n) V
  letI : DiscreteTopology (rowMatrixZLattice V n) := hdisc
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hcount := rowMatrix_lattice_ball_count_height_scaled_uniform
    V hk hn hT₀ hC_R hRadius hR
  have hsum := @lattice_subtype_scaled_sum_le_of_count
    (rowMatrixRealSpan V n) inferInstance inferInstance inferInstance inferInstance
    (rowMatrixZLattice V n) hdisc inferInstance
      (fun A => rowMatrixRank V A = k)
      (fun x : rowMatrixRealSpan V n => |f (x : M n m (K_ℝ[K]))|)
      (h_f.rowMatrix_abs_compactSupport V) (fun x => abs_nonneg _)
      T ((R + 1) * T) C
      (euclideanUnitBallVolume (n * (k * degree K)) *
        (R + 1 + C_R) ^ (n * (k * degree K)) *
        (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)))
      hT₀ hsupport hbound hC hcount
  calc
    (∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
        |f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))|) ≤
        C * (euclideanUnitBallVolume (n * (k * degree K)) *
          (R + 1 + C_R) ^ (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K))) := hsum
    _ = C * euclideanUnitBallVolume (n * (k * degree K)) *
          (R + 1 + C_R) ^ (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)) := by
      ring

/- [derived consequence, paper `le:low_rank_terms`, lines 1558--1568]
   Intrinsic-Voronoi-radius version of the fixed-coefficient rank-filtered
   inner-sum estimate.  Its support and value bounds are unchanged; only the
   paper's `sqrt n * rho(Λ_D)` replaces the auxiliary basis radius. -/
set_option maxHeartbeats 1200000 in
theorem Admissible.rowMatrix_rank_sum_abs_le_of_latticeVoronoi_radius_uniform_of_bounds
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) {T C_R R C : ℝ}
    (hT : 1 ≤ T) (hC_R : 0 ≤ C_R)
    (hRadius :
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) / T ≤ C_R)
    (hR : 0 ≤ R)
    (hsupport : ∀ A : rowMatrixZLattice V n,
      |f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))| ≠ 0 →
        ‖(A : rowMatrixRealSpan V n)‖ ≤ (R + 1) * T)
    (hC : 0 ≤ C)
    (hbound : ∀ A : rowMatrixZLattice V n,
      |(|f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))|)| ≤ C) :
    (∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
      |f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
        M n m (K_ℝ[K]))))|) ≤
      C * euclideanUnitBallVolume (n * (k * degree K)) *
        (R + 1 + C_R) ^ (n * (k * degree K)) *
        (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)) := by
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) :=
    rowMatrixZLattice.discreteTopology (n := n) V
  letI : DiscreteTopology (rowMatrixZLattice V n) := hdisc
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hcount := rowMatrix_lattice_ball_count_height_scaled_uniform_intrinsic
    V hk hn hT₀ hC_R hRadius hR
  have hsum := @lattice_subtype_scaled_sum_le_of_count
    (rowMatrixRealSpan V n) inferInstance inferInstance inferInstance inferInstance
    (rowMatrixZLattice V n) hdisc inferInstance
      (fun A => rowMatrixRank V A = k)
      (fun x : rowMatrixRealSpan V n => |f (x : M n m (K_ℝ[K]))|)
      (h_f.rowMatrix_abs_compactSupport V) (fun x => abs_nonneg _)
      T ((R + 1) * T) C
      (euclideanUnitBallVolume (n * (k * degree K)) *
        (R + 1 + C_R) ^ (n * (k * degree K)) *
        (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)))
      hT₀ hsupport hbound hC hcount
  calc
    (∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
        |f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
          M n m (K_ℝ[K]))))|) ≤
        C * (euclideanUnitBallVolume (n * (k * degree K)) *
          (R + 1 + C_R) ^ (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K))) := hsum
    _ = C * euclideanUnitBallVolume (n * (k * degree K)) *
          (R + 1 + C_R) ^ (n * (k * degree K)) *
          (rowSpaceHeight V)⁻¹ ^ n * T ^ (n * (k * degree K)) := by
      ring

/-- Reindex the abstract row-matrix lattice sum by the integral matrices
whose rows belong to `Λ_D`. -/
theorem tsum_rowMatrixZLattice_eq_integralRowMatrices
    {m k n : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) :
    (∑' A : rowMatrixZLattice V n,
        f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))) =
      ∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
        f (T⁻¹ • embedMatrix A.1) := by
  let e := integralRowMatricesEquivRowMatrixZLattice V n
  simpa [e] using
    (e.tsum_eq (fun A : rowMatrixZLattice V n =>
      f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K])))))).symm

/- The same unrestricted sum can be written as a sum over independent rows,
   using the product equivalence from `RowLattice`. -/
theorem tsum_rowMatrixZLattice_eq_rowTuples
    {m k n : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) :
    (∑' A : rowMatrixZLattice V n,
        f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))) =
      ∑' A : Fin n → rowZLattice V,
        f (T⁻¹ • (fun i j =>
          (((A i : rowZLattice V) : Fin m → K_ℝ[K]) j))) := by
  let e := rowMatrixZLatticeEquiv (n := n) V
  let F : (Fin n → rowZLattice V) → ℝ := fun A =>
    f (T⁻¹ • (fun i j =>
      (((A i : rowZLattice V) : Fin m → K_ℝ[K]) j)))
  calc
    (∑' A : rowMatrixZLattice V n,
        f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))) =
        ∑' A : rowMatrixZLattice V n, F (e A) := by
      apply tsum_congr
      intro A
      congr 1
    _ = ∑' A : Fin n → rowZLattice V, F A := e.tsum_eq F
    _ = ∑' A : Fin n → rowZLattice V,
        f (T⁻¹ • (fun i j =>
          (((A i : rowZLattice V) : Fin m → K_ℝ[K]) j))) := by
      rfl

/-- Reindex the rank-conditioned row-matrix lattice sum by the integral
matrices whose rows lie in `Λ_D` and whose rank is `k`. -/
theorem tsum_rowMatrixZLattice_rank_eq_integralRowMatrices
    {m k n : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) :
    (∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
        f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
          M n m (K_ℝ[K]))))) =
      ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = k},
        f (T⁻¹ • embedMatrix A.1) := by
  let e := rankIntegralRowMatricesEquivRowMatrixZLattice (n := n) V
  simpa [e] using
    (e.tsum_eq
      (fun A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k} =>
        f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
          M n m (K_ℝ[K])))))).symm

theorem summable_rowMatrixTerm
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    Summable (fun A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A} =>
      f (T⁻¹ • embedMatrix A.1)) := by
  exact (summable_scaled_integralMatrices f h_f hT).comp_injective
    Subtype.val_injective

/- [derived consequence, the auxiliary fundamental-parallelepiped route]
   This is the general-lattice estimate for `M_n(Λ_D)` with the arbitrary
   basis radius used internally by the older cell decomposition.  It is not
   the manuscript-facing `ρ` statement; that is formalized separately below. -/
theorem Admissible.rowMatrix_latticeRiemann_estimate
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    (hspan : rowMatrixRealSpan V n ≠ ⊥) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      rowMatrixFundamentalRadius V n / T ≤ 1 →
      |(∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
            f (T⁻¹ • embedMatrix A.1)) /
            T ^ Module.finrank ℝ (rowMatrixRealSpan V n) -
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f| ≤
        Cₐ * rowMatrixFundamentalRadius V n /
          (rowMatrixLatticeCovolume V n * T) := by
  let msX : MeasurableSpace (M n m (K_ℝ[K])) :=
    borel (M n m (K_ℝ[K]))
  let bsX : @BorelSpace (M n m (K_ℝ[K])) inferInstance msX := ⟨rfl⟩
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) := inferInstance
  let hZ := @IsZLattice.mk ℝ inferInstance (rowMatrixRealSpan V n)
    inferInstance inferInstance (rowMatrixZLattice V n) hdisc
    (rowMatrixZLattice_span_top V n)
  obtain ⟨Cₐ, hCₐ, hestimate⟩ :=
    @Admissible.submodule_latticeRiemann_estimate
      (M n m (K_ℝ[K])) inferInstance inferInstance inferInstance
      msX bsX f h_f (rowMatrixRealSpan V n) hspan
      (rowMatrixZLattice V n) hdisc hZ
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  simpa [rowMatrixFundamentalRadius, rowMatrixLatticeCovolume,
    rowMatrixEuclideanMeasure,
    rowMatrixSubspaceIntegral,
    tsum_rowMatrixZLattice_eq_integralRowMatrices V f T] using
    hestimate T hT hRadius

/- [derived consequence of paper `le:without_rank_cond`, lines 1038--1044,
   and `re:help`, lines 550--562, conditional on
   `AdmissibleErrorControlUpTo`] The Riemann estimate for `M_n(Λ_D)` in the
   manuscript's intrinsic-radius notation through an explicitly supplied
   error-control range.  The `RiemannControl` is the restriction of the
   paper's ambient error function; the Euclidean inner-product structure
   below is proved compatible with the already fixed Frobenius norm via
   `rowMatrixRealSpanLpIsometryEquiv`. -/
theorem Admissible.rowMatrix_latticeVoronoiRiemann_estimate_of_errorControlUpTo
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    {εMax : ℝ} (hUpdate : AdmissibleErrorControlUpTo f εMax)
    (hspan : rowMatrixRealSpan V n ≠ ⊥) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) / T ≤ εMax →
      |(∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
            f (T⁻¹ • embedMatrix A.1)) /
            T ^ Module.finrank ℝ (rowMatrixRealSpan V n) -
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f| ≤
        Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
          (rowMatrixLatticeCovolume V n * T) := by
  let msX : MeasurableSpace (M n m (K_ℝ[K])) :=
    borel (M n m (K_ℝ[K]))
  let bsX : @BorelSpace (M n m (K_ℝ[K])) inferInstance msX := ⟨rfl⟩
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) := inferInstance
  let hZ := @IsZLattice.mk ℝ inferInstance (rowMatrixRealSpan V n)
    inferInstance inferInstance (rowMatrixZLattice V n) hdisc
    (rowMatrixZLattice_span_top V n)
  letI : DiscreteTopology (rowMatrixZLattice V n) := hdisc
  letI : @IsZLattice ℝ inferInstance (rowMatrixRealSpan V n)
      inferInstance inferInstance (rowMatrixZLattice V n) hdisc := hZ
  letI : NormedSpace ℝ (rowRealSpan V) :=
    Submodule.normedSpace (rowRealSpan V)
  letI : InnerProductSpace ℝ (rowRealSpan V) :=
    Submodule.innerProductSpace (rowRealSpan V)
  letI : NormedSpace ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V)) :=
    PiLp.normedSpace (p := 2) ℝ _
  letI : InnerProductSpace ℝ (PiLp 2 (fun _ : Fin n => rowRealSpan V)) :=
    PiLp.innerProductSpace _
  letI : InnerProductSpace ℝ (rowMatrixRealSpan V n) :=
    InnerProductSpace.ofNorm ℝ (by
      intro x y
      let e := rowMatrixRealSpanLpIsometryEquiv (n := n) V
      have h := parallelogram_law_with_norm_mul ℝ
        (e x) (e y)
      simpa only [← e.map_add, ← e.map_sub, e.norm_map] using h)
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
  letI : Nontrivial (rowMatrixRealSpan V n) :=
    Submodule.nontrivial_iff_ne_bot.mpr hspan
  obtain ⟨Cₐ, hCₐ, hestimate⟩ :=
    @controlled_latticeVoronoiRiemann_estimate
      (rowMatrixRealSpan V n) inferInstance inferInstance inferInstance inferInstance
      msW bsW inferInstance (rowMatrixZLattice V n) hdisc hZ
      (fun x : rowMatrixRealSpan V n => f (x : M n m (K_ℝ[K])))
      εMax
      (@Admissible.submoduleRiemannControlUpTo
        (M n m (K_ℝ[K])) inferInstance inferInstance inferInstance msX bsX f εMax
        h_f hUpdate (rowMatrixRealSpan V n) hspan)
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  have hcover := rowMatrixZLattice_isLatticeCovering_intrinsic (n := n) V
  have hmatrixRadius :
      latticeCoveringRadius (rowMatrixZLattice V n) ≤
        Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V) :=
    @latticeCoveringRadius_le_of_latticeCovering
      (rowMatrixRealSpan V n) inferInstance inferInstance inferInstance
      (rowMatrixZLattice V n) hdisc hZ _ hcover
  have hmatrixRadiusDiv :
      latticeCoveringRadius (rowMatrixZLattice V n) / T ≤ εMax := by
    calc
      latticeCoveringRadius (rowMatrixZLattice V n) / T ≤
          (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) / T := by
        exact div_le_div_of_nonneg_right hmatrixRadius hT.le
      _ ≤ εMax := hRadius
  have hmain := hestimate T hT hmatrixRadiusDiv
  have hden : 0 < rowMatrixLatticeCovolume V n * T :=
    mul_pos (rowMatrixLatticeCovolume_pos V) hT
  have hfactor : 0 ≤ Cₐ / (rowMatrixLatticeCovolume V n * T) :=
    div_nonneg hCₐ.le hden.le
  have hrhs :
      Cₐ * latticeCoveringRadius (rowMatrixZLattice V n) /
          (rowMatrixLatticeCovolume V n * T) ≤
        Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
          (rowMatrixLatticeCovolume V n * T) := by
    calc
      Cₐ * latticeCoveringRadius (rowMatrixZLattice V n) /
          (rowMatrixLatticeCovolume V n * T) =
          (Cₐ / (rowMatrixLatticeCovolume V n * T)) *
            latticeCoveringRadius (rowMatrixZLattice V n) := by ring
      _ ≤ (Cₐ / (rowMatrixLatticeCovolume V n * T)) *
            (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) :=
          mul_le_mul_of_nonneg_left hmatrixRadius hfactor
      _ = Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
          (rowMatrixLatticeCovolume V n * T) := by ring
  have hmain' :
      |(∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
            f (T⁻¹ • embedMatrix A.1)) /
            T ^ Module.finrank ℝ (rowMatrixRealSpan V n) -
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f| ≤
        Cₐ * latticeCoveringRadius (rowMatrixZLattice V n) /
          (rowMatrixLatticeCovolume V n * T) := by
    simpa [rowMatrixLatticeCovolume, rowMatrixEuclideanMeasure,
      rowMatrixSubspaceIntegral,
      tsum_rowMatrixZLattice_eq_integralRowMatrices V f T] using hmain
  exact hmain'.trans hrhs

/- [paper, `le:without_rank_cond`, lines 1038--1044] The base form of the
   intrinsic-radius Riemann estimate, obtained from the preceding statement
   at the manuscript's original threshold `εMax = 1`. -/
theorem Admissible.rowMatrix_latticeVoronoiRiemann_estimate
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    (hspan : rowMatrixRealSpan V n ≠ ⊥) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) / T ≤ 1 →
      |(∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
            f (T⁻¹ • embedMatrix A.1)) /
            T ^ Module.finrank ℝ (rowMatrixRealSpan V n) -
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f| ≤
        Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
          (rowMatrixLatticeCovolume V n * T) := by
  exact Admissible.rowMatrix_latticeVoronoiRiemann_estimate_of_errorControlUpTo
    V h_f h_f.errorControlUpTo_one hspan

/-- Counting-facing form of the row-matrix estimate.  Under the positive-rank
hypotheses used for fixed-rank matrices, the exponent is the paper's
`n * k * degree K` and the real span is automatically nonzero. -/
theorem Admissible.rowMatrix_latticeRiemann_estimate_rank
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      rowMatrixFundamentalRadius V n / T ≤ 1 →
      |(∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
            f (T⁻¹ • embedMatrix A.1)) /
            T ^ (n * (k * degree K)) -
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f| ≤
        Cₐ * rowMatrixFundamentalRadius V n /
          (rowMatrixLatticeCovolume V n * T) := by
  obtain ⟨Cₐ, hCₐ, hestimate⟩ :=
    h_f.rowMatrix_latticeRiemann_estimate V
      (rowMatrixRealSpan_ne_bot_of_pos V hk hn)
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  simpa [rowMatrixRealSpan_finrank V] using hestimate T hT hRadius

/- [derived consequence of paper `le:without_rank_cond`, lines 1038--1044,
   and `re:help`, lines 550--562, conditional on
   `AdmissibleErrorControlUpTo`] The positive-rank matrix form of the
   intrinsic-radius Riemann estimate through the supplied updated range. -/
theorem Admissible.rowMatrix_latticeVoronoiRiemann_estimate_rank_of_errorControlUpTo
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    {εMax : ℝ} (hUpdate : AdmissibleErrorControlUpTo f εMax)
    (hk : 0 < k) (hn : 0 < n) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) / T ≤ εMax →
      |(∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
            f (T⁻¹ • embedMatrix A.1)) /
            T ^ (n * (k * degree K)) -
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f| ≤
        Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
          (rowMatrixLatticeCovolume V n * T) := by
  obtain ⟨Cₐ, hCₐ, hestimate⟩ :=
    h_f.rowMatrix_latticeVoronoiRiemann_estimate_of_errorControlUpTo V hUpdate
      (rowMatrixRealSpan_ne_bot_of_pos V hk hn)
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  simpa [rowMatrixRealSpan_finrank V] using hestimate T hT hRadius

/- [paper, `le:without_rank_cond`, lines 1038--1044] The positive-rank
   matrix form of the intrinsic-radius Riemann estimate, with the exact
   exponent `n * (k * degree K)` used in the manuscript. -/
theorem Admissible.rowMatrix_latticeVoronoiRiemann_estimate_rank
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) / T ≤ 1 →
      |(∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
            f (T⁻¹ • embedMatrix A.1)) /
            T ^ (n * (k * degree K)) -
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f| ≤
        Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
          (rowMatrixLatticeCovolume V n * T) := by
  obtain ⟨Cₐ, hCₐ, hestimate⟩ :=
    h_f.rowMatrix_latticeVoronoiRiemann_estimate V
      (rowMatrixRealSpan_ne_bot_of_pos V hk hn)
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  simpa [rowMatrixRealSpan_finrank V] using hestimate T hT hRadius

end

end Katznelson
