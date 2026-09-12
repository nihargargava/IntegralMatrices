import Katznelson.Counting.UniformIntegral

/-!
# Uniform intrinsic Voronoi Riemann estimates

This module repairs the order of quantifiers in the row-matrix Riemann estimate
used at `papers/katznelson.tex`, lines 1667--1696.  The admissibility constant,
support radius, and value bound are selected before the varying row space and
scale.  For the arbitrary fixed threshold in Remark `re:help`, lines 550--562,
the proof uses the manuscript's oscillation argument when the normalized
covering radius is at most one and a direct support-ball lattice count above
one.  In particular, no measurability assertion about the large-radius
uncountable supremum defining `errorFunction` is introduced.
-/

namespace Katznelson

open MeasureTheory Set Module
open scoped Classical MeasureTheory NumberField Pointwise

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

section FixedControlledConstant

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/- [Lean infrastructure] Fixed-constant form of
   `controlled_latticeRiemann_estimate_of_fundamentalDomain`.  Its proof is
   the normalization calculation in `ControlledVoronoi.lean`, lines 211--286;
   making the oscillation constant an input prevents Lean from choosing it
   after a varying lattice or subspace has been introduced. -/
theorem controlled_latticeRiemann_estimate_of_fundamentalDomain_fixedConstant
    (F : Set E) (R : ℝ) (hF : MeasurableSet F)
    (hfund : IsAddFundamentalDomain L F
      (μHE[Module.finrank ℝ E] : Measure E))
    (hFbound : ∀ x : E, x ∈ F → ‖x‖ ≤ R) (hRpos : 0 < R)
    (f : E → ℝ) {εMax Cₐ : ℝ} (h : RiemannControl f εMax)
    (hCₐ : 0 < Cₐ)
    (herror : ∀ ε, 0 < ε → ε ≤ εMax →
      ∫ x : E, h.oscillation x ε
        ∂(μHE[Module.finrank ℝ E] : Measure E) ≤ Cₐ * ε) :
    ∀ T : ℝ, 0 < T → R / T ≤ εMax →
      |(∑' v : L, f (T⁻¹ • (v : E))) /
            T ^ Module.finrank ℝ E -
          (ZLattice.covolume L
            (μHE[Module.finrank ℝ E] : Measure E))⁻¹ *
            ∫ x : E, f x
              ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
        Cₐ * R /
          (ZLattice.covolume L
            (μHE[Module.finrank ℝ E] : Measure E) * T) := by
  intro T hT hRadius
  let q : ℕ := Module.finrank ℝ E
  let scale : ℝ := T ^ q
  let covol : ℝ := ZLattice.covolume L
    (μHE[Module.finrank ℝ E] : Measure E)
  let latticeSum : ℝ := ∑' v : L, f (T⁻¹ • (v : E))
  let ambientIntegral : ℝ :=
    ∫ x : E, f x ∂(μHE[Module.finrank ℝ E] : Measure E)
  let ε : ℝ := R / T
  have hε : 0 < ε := div_pos hRpos hT
  have hscale : 0 < scale := pow_pos hT q
  have hraw :=
    controlled_covolume_mul_latticeSum_sub_integral_le_fundamentalDomain
      L F R hF hfund hFbound hRpos f h hT hRadius
  change |covol * latticeSum -
      ∫ x : E, f (T⁻¹ • x)
        ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
    ∫ x : E, h.oscillation (T⁻¹ • x) ε
      ∂(μHE[Module.finrank ℝ E] : Measure E) at hraw
  rw [integral_scaled f hT.le,
    integral_scaled (fun x : E => h.oscillation x ε) hT.le] at hraw
  change |covol * latticeSum - scale * ambientIntegral| ≤
      scale * ∫ x : E, h.oscillation x ε
        ∂(μHE[Module.finrank ℝ E] : Measure E) at hraw
  have herrorε := herror ε hε hRadius
  have hraw' : |covol * latticeSum - scale * ambientIntegral| ≤
      scale * (Cₐ * ε) :=
    hraw.trans (mul_le_mul_of_nonneg_left herrorε hscale.le)
  have hidentity :
      covol * (latticeSum / scale) - ambientIntegral =
        (covol * latticeSum - scale * ambientIntegral) / scale := by
    field_simp [hscale.ne']
  have hnormalized :
      |covol * (latticeSum / scale) - ambientIntegral| ≤ Cₐ * R / T := by
    rw [hidentity, abs_div, abs_of_pos hscale]
    apply (div_le_iff₀ hscale).2
    simpa [ε, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hraw'
  have hcovol : 0 < covol := by
    exact ZLattice.covolume_pos L
      (μHE[Module.finrank ℝ E] : Measure E)
  have hidentity' :
      latticeSum / scale - covol⁻¹ * ambientIntegral =
        (covol * (latticeSum / scale) - ambientIntegral) / covol := by
    field_simp [hcovol.ne']
  have hrhs : Cₐ * R / (covol * T) =
      (Cₐ * R / T) / covol := by
    field_simp [hcovol.ne', hT.ne']
  change |latticeSum / scale - covol⁻¹ * ambientIntegral| ≤
    Cₐ * R / (covol * T)
  rw [hidentity', abs_div, abs_of_pos hcovol, hrhs]
  exact (div_le_div_iff_of_pos_right hcovol).2 hnormalized

/- [derived consequence of paper `le:Riemann_estimate`, lines 574--607]
   The preceding fixed-constant normalization on the intrinsic Voronoi
   domain.  The constant is still an input and therefore can be selected
   before any later-varying lattice. -/
theorem controlled_latticeVoronoiRiemann_estimate_fixedConstant
    (f : E → ℝ) {εMax Cₐ : ℝ} (h : RiemannControl f εMax)
    (hCₐ : 0 < Cₐ)
    (herror : ∀ ε, 0 < ε → ε ≤ εMax →
      ∫ x : E, h.oscillation x ε
        ∂(μHE[Module.finrank ℝ E] : Measure E) ≤ Cₐ * ε) :
    ∀ T : ℝ, 0 < T → latticeCoveringRadius L / T ≤ εMax →
      |(∑' v : L, f (T⁻¹ • (v : E))) /
            T ^ Module.finrank ℝ E -
          (ZLattice.covolume L
            (μHE[Module.finrank ℝ E] : Measure E))⁻¹ *
            ∫ x : E, f x
              ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
        Cₐ * latticeCoveringRadius L /
          (ZLattice.covolume L
            (μHE[Module.finrank ℝ E] : Measure E) * T) := by
  let F : Set E := latticeVoronoiDomain L
  have hF : MeasurableSet F :=
    isClosed_latticeVoronoiDomain L |>.measurableSet
  have hfund : IsAddFundamentalDomain L F
      (μHE[Module.finrank ℝ E] : Measure E) :=
    latticeVoronoiDomain_isAddFundamentalDomain L
      (μHE[Module.finrank ℝ E] : Measure E)
  have hFbound : ∀ x : E, x ∈ F → ‖x‖ ≤ latticeCoveringRadius L := by
    intro x hx
    exact norm_le_latticeCoveringRadius_of_mem_latticeVoronoiDomain L hx
  exact controlled_latticeRiemann_estimate_of_fundamentalDomain_fixedConstant
    L F (latticeCoveringRadius L) hF hfund hFbound
      (latticeCoveringRadius_pos L) f h hCₐ herror

end FixedControlledConstant

section UniformSmallRowEstimate

variable {K : Type*} [Field K] [NumberField K]

/- [paper, Hypothesis `hy:admissible`, lines 532--549, and Lemma
   `le:Riemann_estimate`, lines 574--607] Uniform small-radius specialization
   to `M_n(Λ_D)`.  The single admissibility constant is extracted before
   `V` and `T`; the exact intrinsic radius and covolume are those used at
   lines 1667--1696. -/
set_option maxHeartbeats 1800000 in
theorem Admissible.exists_uniform_rowMatrix_latticeVoronoiRiemann_estimate_rank
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧
      ∀ (V : Grassmannian K m k) (T : ℝ), 0 < T →
        (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) / T ≤ 1 →
        |(∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
              f (T⁻¹ • embedMatrix A.1)) /
              T ^ (n * (k * degree K)) -
            (rowMatrixLatticeCovolume V n)⁻¹ *
              rowMatrixSubspaceIntegral V n f| ≤
          Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
            (rowMatrixLatticeCovolume V n * T) := by
  obtain ⟨Cₐ, hCₐ, herror⟩ := h_f.error_bound
  refine ⟨Cₐ, hCₐ, ?_⟩
  intro V T hT hRadius
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
      have h := parallelogram_law_with_norm_mul ℝ (e x) (e y)
      simpa only [← e.map_add, ← e.map_sub, e.norm_map] using h)
  let msW : MeasurableSpace (rowMatrixRealSpan V n) :=
    @Subtype.instMeasurableSpace (M n m (K_ℝ[K]))
      (fun A => A ∈ rowMatrixRealSpan V n)
      (kRealMatrixMeasurableSpace (K := K))
  letI msWInst : MeasurableSpace (rowMatrixRealSpan V n) := msW
  letI bsWInst : BorelSpace (rowMatrixRealSpan V n) :=
    @Subtype.borelSpace (M n m (K_ℝ[K])) inferInstance
      (kRealMatrixMeasurableSpace (K := K))
      (kRealMatrixBorelSpace (K := K))
      (fun A => A ∈ rowMatrixRealSpan V n)
  have hspan : rowMatrixRealSpan V n ≠ ⊥ :=
    rowMatrixRealSpan_ne_bot_of_pos V hk hn
  letI : Nontrivial (rowMatrixRealSpan V n) :=
    Submodule.nontrivial_iff_ne_bot.mpr hspan
  let control : @RiemannControl (rowMatrixRealSpan V n) inferInstance
      inferInstance msWInst bsWInst
      (fun x : rowMatrixRealSpan V n => f (x : M n m (K_ℝ[K]))) 1 :=
    @Admissible.submoduleRiemannControl
      (M n m (K_ℝ[K])) inferInstance inferInstance inferInstance
      msX bsX f h_f (rowMatrixRealSpan V n) hspan
  have herrorW : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∫ x : rowMatrixRealSpan V n,
          errorFunction f (x : M n m (K_ℝ[K])) ε
        ∂(@Measure.euclideanHausdorffMeasure (rowMatrixRealSpan V n)
          inferInstance msWInst bsWInst
          (Module.finrank ℝ (rowMatrixRealSpan V n))) ≤ Cₐ * ε := by
    intro ε hε hεone
    rw [← @euclideanIntegral_eq_integral (rowMatrixRealSpan V n)
      inferInstance inferInstance msWInst bsWInst]
    exact herror (rowMatrixRealSpan V n) hspan ε hε hεone
  have hcover := rowMatrixZLattice_isLatticeCovering_intrinsic (n := n) V
  have hmatrixRadius :
      latticeCoveringRadius (rowMatrixZLattice V n) ≤
        Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V) :=
    @latticeCoveringRadius_le_of_latticeCovering
      (rowMatrixRealSpan V n) inferInstance inferInstance inferInstance
      (rowMatrixZLattice V n) hdisc hZ _ hcover
  have hmatrixRadiusDiv :
      latticeCoveringRadius (rowMatrixZLattice V n) / T ≤ 1 := by
    calc
      latticeCoveringRadius (rowMatrixZLattice V n) / T ≤
          (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) / T :=
        div_le_div_of_nonneg_right hmatrixRadius hT.le
      _ ≤ 1 := hRadius
  have hmain :=
    @controlled_latticeVoronoiRiemann_estimate_fixedConstant
      (rowMatrixRealSpan V n) inferInstance inferInstance inferInstance
      msWInst bsWInst inferInstance (rowMatrixZLattice V n) hdisc hZ
      (fun x : rowMatrixRealSpan V n => f (x : M n m (K_ℝ[K])))
      1 Cₐ control hCₐ (by
        intro ε hε hεone
        change ∫ x : rowMatrixRealSpan V n,
            errorFunction f (x : M n m (K_ℝ[K])) ε
          ∂(@Measure.euclideanHausdorffMeasure (rowMatrixRealSpan V n)
            inferInstance msWInst bsWInst
            (Module.finrank ℝ (rowMatrixRealSpan V n))) ≤ Cₐ * ε
        exact herrorW ε hε hεone) T hT hmatrixRadiusDiv
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
      _ = Cₐ *
            (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
          (rowMatrixLatticeCovolume V n * T) := by ring
  have hmain' :
      |(∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
            f (T⁻¹ • embedMatrix A.1)) /
            T ^ (n * (k * degree K)) -
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f| ≤
        Cₐ * latticeCoveringRadius (rowMatrixZLattice V n) /
          (rowMatrixLatticeCovolume V n * T) := by
    simpa [rowMatrixLatticeCovolume, rowMatrixEuclideanMeasure,
      rowMatrixSubspaceIntegral, rowMatrixRealSpan_finrank V,
      tsum_rowMatrixZLattice_eq_integralRowMatrices V f T] using hmain
  exact hmain'.trans hrhs

end UniformSmallRowEstimate

section UniformCoarseBounds

variable {K : Type*} [Field K] [NumberField K]

/- [derived consequence of paper `le:ballvol`, lines 463--478, and
   Hypothesis `hy:admissible`, lines 532--549] A support-ball count bounds
   the normalized unrestricted `M_n(Λ_D)` sum uniformly for every row
   space whose normalized intrinsic radius is below a fixed threshold. -/
set_option maxHeartbeats 1800000 in
theorem Admissible.exists_uniform_rowMatrix_latticeAverage_abs_le_of_radius
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) (εMax : ℝ) (hεMax : 0 < εMax) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Grassmannian K m k) (T : ℝ), 0 < T →
        (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) / T ≤
            εMax →
        |(∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
            f (T⁻¹ • embedMatrix A.1)) /
              T ^ (n * (k * degree K))| ≤
          C * (rowMatrixLatticeCovolume V n)⁻¹ := by
  obtain ⟨R, hR, hRsupport⟩ := h_f.exists_support_radius
  obtain ⟨C₀, hC₀, hC₀bound⟩ := h_f.exists_uniform_bound
  let Cval : ℝ := C₀ + 1
  let q : ℕ := n * (k * degree K)
  let C : ℝ := Cval * euclideanUnitBallVolume q *
    (R + 1 + εMax) ^ q
  have hCval : 0 < Cval := by
    dsimp [Cval]
    linarith
  have hbase : 0 < R + 1 + εMax := by linarith
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos hCval (euclideanUnitBallVolume_pos q))
      (pow_pos hbase q)
  refine ⟨C, hC, ?_⟩
  intro V T hT hRadius
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) :=
    rowMatrixZLattice.discreteTopology (n := n) V
  letI : DiscreteTopology (rowMatrixZLattice V n) := hdisc
  have hsupport : ∀ A : rowMatrixZLattice V n,
      f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K])))) ≠ 0 →
        ‖(A : rowMatrixRealSpan V n)‖ ≤ (R + 1) * T := by
    intro A hA
    have hball := hRsupport _ hA
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hT] at hball
    calc
      ‖(A : rowMatrixRealSpan V n)‖ =
          T * (T⁻¹ * ‖(A : rowMatrixRealSpan V n)‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]
      _ ≤ T * R := mul_le_mul_of_nonneg_left hball hT.le
      _ ≤ T * (R + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hT.le
      _ = (R + 1) * T := by ring
  have hbound : ∀ A : rowMatrixZLattice V n,
      |f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))| ≤
        Cval := by
    intro A
    exact (hC₀bound _).trans (by dsimp [Cval]; linarith)
  have hcompactAbs := h_f.rowMatrix_abs_compactSupport V
  have hcompact : HasCompactSupport
      (fun x : rowMatrixRealSpan V n => f (x : M n m (K_ℝ[K]))) := by
    simpa only [HasCompactSupport, tsupport, Function.support, abs_ne_zero]
      using hcompactAbs
  have hcount := rowMatrix_lattice_ball_count_height_scaled_uniform_intrinsic
    V hk hn hT hεMax.le hRadius hR
  have hsumSubtype := @lattice_subtype_scaled_sum_abs_le
    (rowMatrixRealSpan V n) inferInstance inferInstance inferInstance inferInstance
    (rowMatrixZLattice V n) hdisc inferInstance (fun _ => True)
    (fun x : rowMatrixRealSpan V n => f (x : M n m (K_ℝ[K]))) hcompact
    T ((R + 1) * T) Cval hT hsupport hbound hCval.le
  let eTrue : {A : rowMatrixZLattice V n // True} ≃
      rowMatrixZLattice V n :=
    { toFun := fun A => A.1
      invFun := fun A => ⟨A, trivial⟩
      left_inv := fun A => by cases A; rfl
      right_inv := fun _ => rfl }
  have hsumReindex :
      (∑' A : {A : rowMatrixZLattice V n // True},
        f (((T⁻¹ • (A.1 : rowMatrixRealSpan V n) :
          rowMatrixRealSpan V n) : M n m (K_ℝ[K])))) =
      ∑' A : rowMatrixZLattice V n,
        f (((T⁻¹ • (A : rowMatrixRealSpan V n) :
          rowMatrixRealSpan V n) : M n m (K_ℝ[K]))) := by
    exact eTrue.tsum_eq (fun A : rowMatrixZLattice V n =>
      f (((T⁻¹ • (A : rowMatrixRealSpan V n) :
        rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))
  rw [hsumReindex] at hsumSubtype
  have hsum :
      |∑' A : rowMatrixZLattice V n,
          f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))| ≤
        C * (rowSpaceHeight V)⁻¹ ^ n * T ^ q := by
    calc
      |∑' A : rowMatrixZLattice V n,
          f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))| ≤
          Cval * (Set.ncard {A : rowMatrixZLattice V n |
            ‖(A : rowMatrixRealSpan V n)‖ ≤ (R + 1) * T} : ℝ) :=
        hsumSubtype
      _ ≤ Cval * (euclideanUnitBallVolume q *
          (R + 1 + εMax) ^ q * (rowSpaceHeight V)⁻¹ ^ n * T ^ q) :=
        mul_le_mul_of_nonneg_left hcount hCval.le
      _ = C * (rowSpaceHeight V)⁻¹ ^ n * T ^ q := by
        dsimp [C, q]
        ring
  have hscale : 0 < T ^ q := pow_pos hT q
  rw [← tsum_rowMatrixZLattice_eq_integralRowMatrices V f T]
  rw [abs_div, abs_of_pos hscale]
  apply (div_le_iff₀ hscale).2
  simpa [q, rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow, inv_pow,
    mul_assoc] using hsum

end UniformCoarseBounds

section UniformArbitraryThreshold

variable {K : Type*} [Field K] [NumberField K]

/- [derived consequence; author-approved local adaptation of Remark `re:help`,
   lines 550--562, and Lemma `le:Riemann_estimate`, lines 574--607] For every
   fixed positive cutoff, one constant chosen before `V` and `T` gives the
   manuscript's intrinsic row-matrix Riemann estimate.  The branch
   `r / T ≤ 1` is exactly the paper's error-function proof.  In the complementary
   branch we use compact support and a uniform lattice-point count instead of
   extending the paper's error-function argument to large radii.  The author
   explicitly permits this deviation only for this local step; the theorem's
   statement and every downstream normalization remain unchanged. -/
set_option maxHeartbeats 1800000 in
theorem Admissible.exists_uniform_rowMatrix_latticeVoronoiRiemann_estimate_rank_upTo
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) (εMax : ℝ) (hεMax : 0 < εMax) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧
      ∀ (V : Grassmannian K m k) (T : ℝ), 0 < T →
        (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) / T ≤
            εMax →
        |(∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
              f (T⁻¹ • embedMatrix A.1)) /
              T ^ (n * (k * degree K)) -
            (rowMatrixLatticeCovolume V n)⁻¹ *
              rowMatrixSubspaceIntegral V n f| ≤
          Cₐ *
              (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
            (rowMatrixLatticeCovolume V n * T) := by
  obtain ⟨Csmall, hCsmall, hsmall⟩ :=
    h_f.exists_uniform_rowMatrix_latticeVoronoiRiemann_estimate_rank f hk hn
  obtain ⟨Csum, hCsum, hsum⟩ :=
    h_f.exists_uniform_rowMatrix_latticeAverage_abs_le_of_radius
      f hk hn εMax hεMax
  obtain ⟨Cint, hCint, hintegral⟩ :=
    h_f.exists_uniform_rowMatrixSubspaceIntegral_abs_le f hn hk
  let Cₐ : ℝ := Csmall + Csum + Cint
  have hCₐ : 0 < Cₐ := by
    dsimp [Cₐ]
    linarith
  refine ⟨Cₐ, hCₐ, ?_⟩
  intro V T hT hRadius
  let r : ℝ :=
    Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)
  let covol : ℝ := rowMatrixLatticeCovolume V n
  have hr : 0 ≤ r := by
    dsimp [r]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (latticeCoveringRadius_nonneg _)
  have hcovol : 0 < covol := by
    dsimp [covol]
    exact rowMatrixLatticeCovolume_pos V
  have hfactor : 0 ≤ r / (covol * T) :=
    div_nonneg hr (mul_nonneg hcovol.le hT.le)
  by_cases hunit : r / T ≤ 1
  · have hbase := hsmall V T hT hunit
    have hcoeff : Csmall ≤ Cₐ := by
      dsimp [Cₐ]
      linarith
    have hscaled : Csmall * r / (covol * T) ≤
        Cₐ * r / (covol * T) := by
      calc
        Csmall * r / (covol * T) =
            Csmall * (r / (covol * T)) := by ring
        _ ≤ Cₐ * (r / (covol * T)) :=
          mul_le_mul_of_nonneg_right hcoeff hfactor
        _ = Cₐ * r / (covol * T) := by ring
    exact hbase.trans (by simpa [r, covol] using hscaled)
  · have hlarge : 1 < r / T := lt_of_not_ge hunit
    have hsumBound := hsum V T hT (by simpa [r] using hRadius)
    have hintegralBound := hintegral V
    have hcovolInv : 0 ≤ covol⁻¹ := inv_nonneg.mpr hcovol.le
    have hmainTerm :
        |covol⁻¹ * rowMatrixSubspaceIntegral V n f| ≤ Cint * covol⁻¹ := by
      calc
        |covol⁻¹ * rowMatrixSubspaceIntegral V n f| =
            covol⁻¹ * |rowMatrixSubspaceIntegral V n f| := by
          rw [abs_mul, abs_of_nonneg hcovolInv]
        _ ≤ covol⁻¹ * Cint :=
          mul_le_mul_of_nonneg_left hintegralBound hcovolInv
        _ = Cint * covol⁻¹ := by ring
    have hcoeffBase : Csum + Cint ≤ Cₐ := by
      dsimp [Cₐ]
      linarith
    have hcoeffScale : Cₐ ≤ Cₐ * (r / T) := by
      calc
        Cₐ = Cₐ * 1 := by ring
        _ ≤ Cₐ * (r / T) :=
          mul_le_mul_of_nonneg_left hlarge.le hCₐ.le
    have hcoarse : (Csum + Cint) * covol⁻¹ ≤
        Cₐ * (r / T) * covol⁻¹ :=
      mul_le_mul_of_nonneg_right
        (hcoeffBase.trans hcoeffScale) hcovolInv
    calc
      |(∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
            f (T⁻¹ • embedMatrix A.1)) /
            T ^ (n * (k * degree K)) -
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f| ≤
          |(∑' A : {A : IntegralMatrix K n m //
              rowsInIntegralRowModule V A},
              f (T⁻¹ • embedMatrix A.1)) /
              T ^ (n * (k * degree K))| +
            |(rowMatrixLatticeCovolume V n)⁻¹ *
              rowMatrixSubspaceIntegral V n f| := by
        simpa using (abs_sub_le
          ((∑' A : {A : IntegralMatrix K n m //
              rowsInIntegralRowModule V A},
              f (T⁻¹ • embedMatrix A.1)) /
              T ^ (n * (k * degree K))) 0
          ((rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f))
      _ ≤ Csum * covol⁻¹ + Cint * covol⁻¹ := by
        exact add_le_add (by simpa [covol] using hsumBound)
          (by simpa [covol] using hmainTerm)
      _ = (Csum + Cint) * covol⁻¹ := by ring
      _ ≤ Cₐ * (r / T) * covol⁻¹ := hcoarse
      _ = Cₐ *
            (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
          (rowMatrixLatticeCovolume V n * T) := by
        dsimp [r, covol]
        field_simp [hT.ne', (rowMatrixLatticeCovolume_pos V).ne']

end UniformArbitraryThreshold

section RankRestoration

variable {K : Type*} [Field K] [NumberField K]

/- [paper, Lemma `le:without_rank_cond`, lines 1038--1061, and equations
   (19)--(21), lines 1671--1679] For a fixed row space, partition the
   manuscript's unrestricted integral-matrix sum into rank `k` and strictly
   lower-rank terms. -/
theorem rowSpaceSum_eq_rank_add_lower_uniformRiemann
    {n m k : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    (∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
      f (T⁻¹ • embedMatrix A.1)) =
      (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A = k},
        f (T⁻¹ • embedMatrix A.1)) +
      (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1)) := by
  let g : IntegralMatrix K n m → ℝ := fun A =>
    f (T⁻¹ • embedMatrix A)
  let S : Set (IntegralMatrix K n m) :=
    {A | rowsInIntegralRowModule V A}
  let R : Set (IntegralMatrix K n m) :=
    {A | rowsInIntegralRowModule V A ∧ integralMatrixRank A = k}
  let L : Set (IntegralMatrix K n m) :=
    {A | rowsInIntegralRowModule V A ∧ integralMatrixRank A < k}
  have hsum (U : Set (IntegralMatrix K n m)) :
      Summable (fun A : IntegralMatrix K n m => U.indicator g A) := by
    apply summable_of_hasFiniteSupport
    refine (finite_scaledSupport_integralMatrices f h_f hT).subset ?_
    intro A hA
    by_contra hzero
    have hgzero : g A = 0 := not_ne_iff.mp hzero
    apply hA
    simp [g, hgzero]
  have hsplit (A : IntegralMatrix K n m) :
      S.indicator g A = R.indicator g A + L.indicator g A := by
    by_cases hrows : rowsInIntegralRowModule V A
    · have hle := integralMatrixRank_le_of_rowsInIntegralRowModule V A hrows
      obtain hEq | hLt := eq_or_lt_of_le hle
      · simp [S, R, L, hrows, hEq]
      · simp [S, R, L, hrows, hLt, Nat.ne_of_lt hLt]
    · simp [S, R, L, hrows]
  have hS := hsum S
  have hR := hsum R
  have hL := hsum L
  calc
    (∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
        g A) =
        ∑' A : IntegralMatrix K n m, S.indicator g A :=
      tsum_subtype S g
    _ = ∑' A : IntegralMatrix K n m,
        (R.indicator g A + L.indicator g A) := by
      exact tsum_congr hsplit
    _ = (∑' A : IntegralMatrix K n m, R.indicator g A) +
        (∑' A : IntegralMatrix K n m, L.indicator g A) :=
      hR.tsum_add hL
    _ = (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A = k}, g A) +
        (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A < k}, g A) := by
      rw [(tsum_subtype R g).symm, (tsum_subtype L g).symm]
      rfl
    _ = (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A = k},
        f (T⁻¹ • embedMatrix A.1)) +
        (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1)) := by
      rfl

/- [derived consequence of the preceding paper split and the row-lattice
   reindexings in `RowLatticeRiemann.lean`, lines 1008--1058] The same
   identity in the exact `M_n(Λ_D)` notation consumed by rank restoration. -/
theorem rowMatrixZLatticeSum_eq_rank_add_lower_uniformRiemann
    {n m k : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    (∑' A : rowMatrixZLattice V n,
      f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))) =
      (∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
        f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
          M n m (K_ℝ[K]))))) +
      (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1)) := by
  rw [tsum_rowMatrixZLattice_eq_integralRowMatrices V f T]
  rw [rowSpaceSum_eq_rank_add_lower_uniformRiemann V f h_f hT]
  rw [← tsum_rowMatrixZLattice_rank_eq_integralRowMatrices V f T]

/- [paper, equations (19)--(21), lines 1667--1696] Uniform intrinsic
   Voronoi Riemann estimate after restoring the rank condition.  The
   constant is selected before every row space and scale, the displayed
   `sqrt n * ρ(Λ_D)` and covolume are unchanged, and the strictly lower-rank
   sum appears as the manuscript's absolute correction term. -/
set_option maxHeartbeats 1800000 in
theorem Admissible.exists_uniform_rowMatrix_rank_latticeVoronoi_estimate_with_lower_upTo
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) (εMax : ℝ) (hεMax : 0 < εMax) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧
      ∀ (V : Grassmannian K m k) (T : ℝ), 0 < T →
        (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) / T ≤
            εMax →
        |(∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
            f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
              M n m (K_ℝ[K]))))) /
              T ^ (n * (k * degree K)) -
            (rowMatrixLatticeCovolume V n)⁻¹ *
              rowMatrixSubspaceIntegral V n f| ≤
          Cₐ *
              (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
            (rowMatrixLatticeCovolume V n * T) +
          |(∑' A : {A : IntegralMatrix K n m //
              rowsInIntegralRowModule V A ∧ integralMatrixRank A < k},
            f (T⁻¹ • embedMatrix A.1))| /
              T ^ (n * (k * degree K)) := by
  obtain ⟨Cₐ, hCₐ, hestimate⟩ :=
    h_f.exists_uniform_rowMatrix_latticeVoronoiRiemann_estimate_rank_upTo
      f hk hn εMax hεMax
  refine ⟨Cₐ, hCₐ, ?_⟩
  intro V T hT hRadius
  let q : ℝ := T ^ (n * (k * degree K))
  let R : ℝ :=
    ∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
      f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))
  let L : ℝ :=
    ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A < k},
      f (T⁻¹ • embedMatrix A.1)
  let M : ℝ := (rowMatrixLatticeCovolume V n)⁻¹ *
    rowMatrixSubspaceIntegral V n f
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hsplit :=
    rowMatrixZLatticeSum_eq_rank_add_lower_uniformRiemann V f h_f hT
  have hmain := hestimate V T hT hRadius
  rw [← tsum_rowMatrixZLattice_eq_integralRowMatrices V f T] at hmain
  rw [hsplit] at hmain
  have hmain' : |(R + L) / q - M| ≤
      Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
        (rowMatrixLatticeCovolume V n * T) := by
    simpa [R, L, q, M] using hmain
  change |R / q - M| ≤
      Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
        (rowMatrixLatticeCovolume V n * T) + |L| / q
  calc
    |R / q - M| = |(R + L) / q - M - L / q| := by
      congr 1
      field_simp [hq.ne']
      ring
    _ ≤ |(R + L) / q - M| + |L / q| := by
      simpa using (abs_sub_le ((R + L) / q - M) 0 (L / q))
    _ ≤ Cₐ *
          (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
          (rowMatrixLatticeCovolume V n * T) + |L| / q := by
      rw [abs_div, abs_of_pos hq]
      exact add_le_add hmain' le_rfl

end RankRestoration

end Katznelson
