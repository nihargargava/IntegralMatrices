import Katznelson.Counting.RowLatticeRiemann

/-!
# Uniform bounds for the manuscript's subspace integrals

The tail estimate in `co:tail` uses that the integral of an admissible
function over every row-matrix subspace is bounded by one constant depending
only on the fixed ambient data and the function.  This module derives that
bound from compact support and boundedness, while retaining the exact
`rowMatrixSubspaceIntegral` occurring in the manuscript-facing main term.
-/

namespace Katznelson

open MeasureTheory Set Metric Module
open scoped Classical MeasureTheory NumberField

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

/- [derived consequence of paper Hypothesis `hy:admissible`, lines 532--548,
   used in Lemma `le:schmidt_makes_c1_finite`, lines 837--858, and Corollary
   `co:tail`, lines 1156--1170] Compact support and boundedness give one
   bound for the manuscript's integrals over all rank-`k` row-matrix
   subspaces.  Their common real dimension is `n * k * degree K`, so the
   enclosing-ball volume is independent of the row space. -/
set_option maxHeartbeats 1200000 in
theorem Admissible.exists_uniform_rowMatrixSubspaceIntegral_abs_le
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hn : 0 < n) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : Grassmannian K m k,
      |rowMatrixSubspaceIntegral V n f| ≤ C := by
  obtain ⟨R, hR⟩ := h_f.compactSupport.isBounded.subset_closedBall
    (0 : M n m (K_ℝ[K]))
  obtain ⟨Bval, hBval⟩ := h_f.bounded.subset_closedBall (0 : ℝ)
  let R₀ : ℝ := max R 0 + 1
  let M₀ : ℝ := max Bval 0 + 1
  let q : ℕ := n * (k * degree K)
  let C : ℝ := M₀ * R₀ ^ q * euclideanUnitBallVolume q
  have hR₀ : 0 < R₀ := by
    dsimp [R₀]
    linarith [le_max_right R 0]
  have hM₀ : 0 < M₀ := by
    dsimp [M₀]
    linarith [le_max_right Bval 0]
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos hM₀ (pow_pos hR₀ q))
      (euclideanUnitBallVolume_pos q)
  refine ⟨C, hC, ?_⟩
  intro V
  let ball : Set (rowMatrixRealSpan V n) := closedBall 0 R₀
  have hzero : ∀ x : rowMatrixRealSpan V n, x ∉ ball →
      f (x : M n m (K_ℝ[K])) = 0 := by
    intro x hx
    by_contra hfx
    have hsupport : (x : M n m (K_ℝ[K])) ∈ tsupport f :=
      subset_closure hfx
    have hxR : ‖(x : M n m (K_ℝ[K]))‖ ≤ R := by
      simpa [mem_closedBall, dist_zero_right] using hR hsupport
    have hxR₀ : ‖(x : M n m (K_ℝ[K]))‖ ≤ R₀ := hxR.trans (by
      dsimp [R₀]
      linarith [le_max_left R 0])
    apply hx
    rw [show ball = closedBall 0 R₀ by rfl, mem_closedBall, dist_zero_right]
    change ‖(x : M n m (K_ℝ[K]))‖ ≤ R₀
    exact hxR₀
  have hvalue : ∀ x : rowMatrixRealSpan V n,
      ‖f (x : M n m (K_ℝ[K]))‖ ≤ M₀ := by
    intro x
    have hxmem : f (x : M n m (K_ℝ[K])) ∈ Set.range f := by
      exact ⟨(x : M n m (K_ℝ[K])), rfl⟩
    have hx := hBval hxmem
    have hxM : |f (x : M n m (K_ℝ[K]))| ≤ Bval := by
      simpa [dist_comm, Real.dist_0_eq_abs] using hx
    rw [Real.norm_eq_abs]
    exact hxM.trans (by
      dsimp [M₀]
      linarith [le_max_left Bval 0])
  let msX : MeasurableSpace (M n m (K_ℝ[K])) :=
    borel (M n m (K_ℝ[K]))
  let bsX : @BorelSpace (M n m (K_ℝ[K])) inferInstance msX := ⟨rfl⟩
  let msW : MeasurableSpace (rowMatrixRealSpan V n) :=
    @Subtype.instMeasurableSpace (M n m (K_ℝ[K]))
      (fun x => x ∈ rowMatrixRealSpan V n) msX
  let bsW : @BorelSpace (rowMatrixRealSpan V n) inferInstance msW :=
    @Subtype.borelSpace (M n m (K_ℝ[K])) inferInstance msX bsX
      (fun x => x ∈ rowMatrixRealSpan V n)
  letI msWI : MeasurableSpace (rowMatrixRealSpan V n) := msW
  letI bsWI : BorelSpace (rowMatrixRealSpan V n) := bsW
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
  letI ipsWI : InnerProductSpace ℝ (rowMatrixRealSpan V n) := ipsW
  let mu : Measure (rowMatrixRealSpan V n) :=
    @Measure.euclideanHausdorffMeasure (rowMatrixRealSpan V n)
      inferInstance msW bsW (Module.finrank ℝ (rowMatrixRealSpan V n))
  letI nt : Nontrivial (rowMatrixRealSpan V n) :=
    Submodule.nontrivial_iff_ne_bot.mpr
      (rowMatrixRealSpan_ne_bot_of_pos V hk hn)
  let hhaar : mu.IsAddHaarMeasure := by
    change (@Measure.euclideanHausdorffMeasure (rowMatrixRealSpan V n)
      inferInstance msW bsW (Module.finrank ℝ (rowMatrixRealSpan V n))).IsAddHaarMeasure
    exact @MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure
      (rowMatrixRealSpan V n) inferInstance inferInstance inferInstance msW bsW
  letI hhaarI : mu.IsAddHaarMeasure := hhaar
  letI hfiniteI : IsFiniteMeasureOnCompacts mu :=
    hhaar.toIsFiniteMeasureOnCompacts
  have hmeasure : mu.real ball =
      R₀ ^ q * euclideanUnitBallVolume q := by
    have hscale : mu.real (closedBall 0 R₀) =
        R₀ ^ Module.finrank ℝ (rowMatrixRealSpan V n) *
          mu.real (closedBall 0 1) :=
      @Measure.addHaar_real_closedBall' (rowMatrixRealSpan V n)
        inferInstance inferInstance msW bsW inferInstance mu hhaar
        0 R₀ hR₀.le
    have hunit : mu.real (closedBall 0 1) =
        euclideanUnitBallVolume
          (Module.finrank ℝ (rowMatrixRealSpan V n)) := by
      dsimp [mu]
      exact @euclideanHausdorffMeasureReal_unitClosedBall
        (rowMatrixRealSpan V n) inferInstance ipsW inferInstance
        msW bsW nt
    rw [show ball = closedBall 0 R₀ by rfl, hscale, hunit]
    simp only [rowMatrixRealSpan_finrank V, q]
  have hballfinite : mu ball < ⊤ := by
    rw [show ball = closedBall 0 R₀ by rfl]
    exact @measure_closedBall_lt_top (rowMatrixRealSpan V n) msW
      inferInstance inferInstance mu hfiniteI 0 R₀
  have hsetIntegral :
      ‖∫ x in ball, f (x : M n m (K_ℝ[K])) ∂mu‖ ≤
        M₀ * mu.real ball := by
    exact norm_setIntegral_le_of_norm_le_const
      hballfinite (fun x _ => hvalue x)
  have hintegral :
      (∫ x in ball, f (x : M n m (K_ℝ[K])) ∂mu) =
        ∫ x, f (x : M n m (K_ℝ[K])) ∂mu :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  have hrowIntegral : rowMatrixSubspaceIntegral V n f =
      ∫ x, f (x : M n m (K_ℝ[K])) ∂mu := by
    rfl
  calc
    |rowMatrixSubspaceIntegral V n f| =
        ‖∫ x, f (x : M n m (K_ℝ[K])) ∂mu‖ := by
      rw [hrowIntegral, Real.norm_eq_abs]
    _ = ‖∫ x in ball, f (x : M n m (K_ℝ[K])) ∂mu‖ := by
      rw [hintegral]
    _ ≤ M₀ * mu.real ball := hsetIntegral
    _ = C := by
      rw [hmeasure]
      dsimp [C]
      ring

/- [derived consequence of the preceding paper input] This is the exact
   domination hypothesis consumed by the formalized Schmidt/Abel tail. -/
theorem Admissible.exists_uniform_mainSummand_integral_domination
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hn : 0 < n) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : Grassmannian K m k,
      1 ≤ rowSpaceHeight V →
      |(rowSpaceHeight V)⁻¹ ^ n * rowMatrixSubspaceIntegral V n f| ≤
        C * (rowSpaceHeight V)⁻¹ ^ n := by
  obtain ⟨C, hC, hbound⟩ :=
    h_f.exists_uniform_rowMatrixSubspaceIntegral_abs_le f hn hk
  refine ⟨C, hC, ?_⟩
  intro V _hV
  have hfactor : 0 ≤ (rowSpaceHeight V)⁻¹ ^ n := by positivity
  rw [abs_mul, abs_of_nonneg hfactor]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (hbound V) hfactor

end Katznelson
