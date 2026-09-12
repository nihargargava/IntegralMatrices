import Katznelson.Counting.MinimaSums
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# The critical higher-rank successive-minima sum

This module formalizes the remaining degree-one case of the manuscript's
radius-sum argument (`n = m + 1`, `k ≥ 2`).  In particular it proves the
projection-slab lattice count displayed at lines 1793--1799 using the same
fundamental-domain geometry as the paper's lattice ball count.
-/

namespace Katznelson

open MeasureTheory Set Module
open scoped Classical MeasureTheory NumberField Pointwise

/- [Lean infrastructure] Euclidean volume of a projection slab is bounded
   by the product of the corresponding balls in a subspace and its
   orthogonal complement.  This is the measure-theoretic encoding used for
   the paper's slab at lines 1793--1799. -/
theorem euclideanHausdorffMeasureReal_projection_slab_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (s : Submodule ℝ E) [s.HasOrthogonalProjection]
    {r X : ℝ} (_hr : 0 ≤ r) (_hX : 0 ≤ X) :
    (μHE[Module.finrank ℝ E] : Measure E).real
        {x : E | ‖s.starProjection x‖ ≤ r ∧ ‖x‖ ≤ X} ≤
      ((μHE[Module.finrank ℝ s] : Measure s).real
          (Metric.closedBall (0 : s) r)) *
        ((μHE[Module.finrank ℝ sᗮ] : Measure sᗮ).real
          (Metric.closedBall (0 : sᗮ) X)) := by
  let A : Set E := {x : E | ‖s.starProjection x‖ ≤ r ∧ ‖x‖ ≤ X}
  let P : Set (s × sᗮ) :=
    Metric.closedBall (0 : s) r ×ˢ Metric.closedBall (0 : sᗮ) X
  let e : E ≃ᵐ s × sᗮ := s.measurableEquivProd (0 : E)
  have hsub : A ⊆ e ⁻¹' P := by
    intro x hx
    change e x ∈ P
    rw [show e x =
        (s.orthogonalProjectionOnto x, sᗮ.orthogonalProjectionOnto x) by
      simp [e]]
    constructor
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact hx.1
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (sᗮ.norm_orthogonalProjectionOnto_apply_le x).trans hx.2
  have hPmeas : MeasurableSet P := by
    exact measurableSet_closedBall.prod measurableSet_closedBall
  have hmp : MeasurePreserving e
      (μHE[Module.finrank ℝ E] : Measure E) := by
    exact s.measurePreserving_measurableEquivProd (0 : E)
  have hPtop : (volume : Measure (s × sᗮ)) P ≠ ⊤ := by
    dsimp [P]
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_closedBall_lt_top.ne
      measure_closedBall_lt_top.ne
  have hpretop :
      (μHE[Module.finrank ℝ E] : Measure E) (e ⁻¹' P) ≠ ⊤ := by
    rw [hmp.measure_preimage hPmeas.nullMeasurableSet]
    exact hPtop
  calc
    (μHE[Module.finrank ℝ E] : Measure E).real A ≤
        (μHE[Module.finrank ℝ E] : Measure E).real (e ⁻¹' P) :=
      measureReal_mono hsub hpretop
    _ = (volume : Measure (s × sᗮ)).real P :=
      hmp.measureReal_preimage hPmeas.nullMeasurableSet
    _ = ((μHE[Module.finrank ℝ s] : Measure s).real
          (Metric.closedBall (0 : s) r)) *
        ((μHE[Module.finrank ℝ sᗮ] : Measure sᗮ).real
          (Metric.closedBall (0 : sᗮ) X)) := by
      rw [Measure.volume_eq_prod, measureReal_prod_prod]
      rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := s),
        ← InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := sᗮ)]

/- [Lean infrastructure] Fundamental-domain counting in a projection slab.
   The specialized theorem below bridges this general Euclidean statement
   back to the exact ambient lattice and projection of paper lines
   1793--1799. -/
set_option maxHeartbeats 1200000 in
theorem lattice_projection_slab_count
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : Submodule ℝ E) [s.HasOrthogonalProjection]
    [Nontrivial s] [Nontrivial sᗮ]
    {r X : ℝ} (hr : 0 ≤ r) (hX : 0 ≤ X) :
    (Set.ncard {v : L |
        ‖s.starProjection (v : E)‖ ≤ r ∧ ‖(v : E)‖ ≤ X} : ℝ) ≤
      ((r + latticeFundamentalRadius L) ^ Module.finrank ℝ s *
        euclideanUnitBallVolume (Module.finrank ℝ s) *
        ((X + latticeFundamentalRadius L) ^ Module.finrank ℝ sᗮ *
          euclideanUnitBallVolume (Module.finrank ℝ sᗮ))) *
        (ZLattice.covolume L
          (μHE[Module.finrank ℝ E] : Measure E))⁻¹ := by
  let S : Set L := {v : L |
    ‖s.starProjection (v : E)‖ ≤ r ∧ ‖(v : E)‖ ≤ X}
  let F : Set E := latticeFundamentalDomain L
  let R : ℝ := latticeFundamentalRadius L
  let mu : Measure E := μHE[Module.finrank ℝ E]
  have hS : S.Finite := by
    apply (lattice_ball_finite L).subset
    intro v hv
    exact hv.2
  have hR : 0 ≤ R := latticeFundamentalRadius_nonneg L
  have hrR : 0 ≤ r + R := add_nonneg hr hR
  have hXR : 0 ≤ X + R := add_nonneg hX hR
  have hFtop : mu F ≠ ⊤ :=
    ne_of_lt (latticeFundamentalDomain_isBounded L).measure_lt_top
  have hfund : IsAddFundamentalDomain L F mu :=
    latticeFundamentalDomain_isAddFundamentalDomain L mu
  have hunion :
      (⋃ v ∈ hS.toFinset, (v : E) +ᵥ F) ⊆
        {x : E | ‖s.starProjection x‖ ≤ r + R ∧ ‖x‖ ≤ X + R} := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨v, hv, hx⟩
    have hvS : v ∈ S := hS.mem_toFinset.mp hv
    rcases Set.mem_vadd_set.mp hx with ⟨y, hy, hxy⟩
    have hyR : ‖y‖ ≤ R := norm_le_latticeFundamentalRadius L hy
    constructor
    · rw [← hxy, vadd_eq_add]
      calc
        ‖s.starProjection ((v : E) + y)‖ =
            ‖s.starProjection (v : E) + s.starProjection y‖ := by rw [map_add]
        _ ≤
            ‖s.starProjection (v : E)‖ + ‖s.starProjection y‖ := norm_add_le _ _
        _ ≤ r + R := add_le_add hvS.1
          ((s.norm_starProjection_apply_le y).trans hyR)
    · rw [← hxy, vadd_eq_add]
      exact (norm_add_le _ _).trans (add_le_add hvS.2 hyR)
  have hmeasure :
      mu.real (⋃ v ∈ hS.toFinset, (v : E) +ᵥ F) =
        (hS.toFinset.card : ℝ) * mu.real F := by
    rw [measureReal_biUnion_finset₀
      (hd := by
        intro v hv w hw hvw
        exact hfund.aedisjoint hvw)
      (hm := by
        intro v hv
        exact hfund.nullMeasurableSet.vadd (v : E))
      (h := by
        intro v hv
        rw [MeasureTheory.measure_vadd mu (v : E)]
        exact hFtop)]
    simp [MeasureTheory.measureReal_def, MeasureTheory.measure_vadd]
  have hslab := euclideanHausdorffMeasureReal_projection_slab_le
    (s := s) hrR hXR
  have hslabtop :
      mu {x : E | ‖s.starProjection x‖ ≤ r + R ∧ ‖x‖ ≤ X + R} ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt
      (measure_mono (show {x : E |
          ‖s.starProjection x‖ ≤ r + R ∧ ‖x‖ ≤ X + R} ⊆
            Metric.closedBall (0 : E) (X + R) by
        intro x hx
        simpa [Metric.mem_closedBall, dist_zero_right] using hx.2))
    exact measure_closedBall_lt_top
  have hmeasure_le :
      (hS.toFinset.card : ℝ) * mu.real F ≤
        (r + R) ^ Module.finrank ℝ s *
          euclideanUnitBallVolume (Module.finrank ℝ s) *
          ((X + R) ^ Module.finrank ℝ sᗮ *
            euclideanUnitBallVolume (Module.finrank ℝ sᗮ)) := by
    rw [← hmeasure]
    calc
      mu.real (⋃ v ∈ hS.toFinset, (v : E) +ᵥ F) ≤
          mu.real {x : E |
            ‖s.starProjection x‖ ≤ r + R ∧ ‖x‖ ≤ X + R} :=
        measureReal_mono hunion hslabtop
      _ ≤
          (μHE[Module.finrank ℝ s] : Measure s).real
              (Metric.closedBall (0 : s) (r + R)) *
            (μHE[Module.finrank ℝ sᗮ] : Measure sᗮ).real
              (Metric.closedBall (0 : sᗮ) (X + R)) := hslab
      _ = (r + R) ^ Module.finrank ℝ s *
          euclideanUnitBallVolume (Module.finrank ℝ s) *
          ((X + R) ^ Module.finrank ℝ sᗮ *
            euclideanUnitBallVolume (Module.finrank ℝ sᗮ)) := by
        rw [MeasureTheory.Measure.addHaar_real_closedBall'
            (μHE[Module.finrank ℝ s] : Measure s) 0 hrR,
          MeasureTheory.Measure.addHaar_real_closedBall'
            (μHE[Module.finrank ℝ sᗮ] : Measure sᗮ) 0 hXR,
          euclideanHausdorffMeasureReal_unitClosedBall,
          euclideanHausdorffMeasureReal_unitClosedBall]
  have hcovpos : 0 < ZLattice.covolume L mu := ZLattice.covolume_pos L mu
  have hcard :
      (Set.ncard S : ℝ) * ZLattice.covolume L mu ≤
        (r + R) ^ Module.finrank ℝ s *
          euclideanUnitBallVolume (Module.finrank ℝ s) *
          ((X + R) ^ Module.finrank ℝ sᗮ *
            euclideanUnitBallVolume (Module.finrank ℝ sᗮ)) := by
    rw [Set.ncard_eq_toFinset_card S hS,
      covolume_eq_measureReal_latticeFundamentalDomain L mu]
    exact hmeasure_le
  have hdiv := (le_div_iff₀ hcovpos).2 hcard
  simpa [S, R, mu, div_eq_mul_inv] using hdiv

/- [Lean infrastructure for paper lines 1761 and 1793--1799] In degree
   one, the manuscript's `K_ℝ`-line generated by a nonzero row is a real
   line. -/
theorem rowAmbientScalarLine_finrank_eq_one_of_degree_one
    {K : Type*} [Field K] [NumberField K] {m : ℕ}
    (hdegree : degree K = 1) {x : RowVector K m} (hx : x ≠ 0) :
    Module.finrank ℝ (rowAmbientScalarLine (K := K) (m := m) x) = 1 := by
  let f : K_ℝ[K] →ₗ[ℝ] RowVector K m :=
    rowAmbientScalarMultiplicationMap (K := K) (m := m) x
  have hdomain : Module.finrank ℝ K_ℝ[K] = 1 := by
    rw [NumberField.mixedEmbedding.euclidean.finrank]
    exact hdegree
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro c hc
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hdomain
      (one_ne_zero : (1 : K_ℝ[K]) ≠ 0) c
    have hfx : f 1 = x := by
      change (1 : K_ℝ[K]) • x = x
      exact one_smul _ x
    have hasmul : a • x = 0 := by
      rw [← hfx, ← map_smul, ha]
      exact hc
    have ha0 : a = 0 := (smul_eq_zero.mp hasmul).resolve_right hx
    rw [← ha, ha0, zero_smul]
  change Module.finrank ℝ f.range = 1
  rw [LinearMap.finrank_range_of_inj hinj, hdomain]

/- [Lean infrastructure] Canonical Borel instances for the `PiLp` row
   abbreviation, needed by the volume argument below. -/
noncomputable local instance criticalAmbientRowMeasurableSpace
    {K : Type*} [Field K] [NumberField K] {m : ℕ} :
    MeasurableSpace (RowVector K m) := borel (RowVector K m)

local instance criticalAmbientRowBorelSpace
    {K : Type*} [Field K] [NumberField K] {m : ℕ} :
    BorelSpace (RowVector K m) := ⟨rfl⟩

/- [paper: displayed slab count, lines 1793--1799] This is the manuscript's
   slab count for the fixed ambient lattice in degree one.  The constants
   introduced by the fundamental parallelepiped are absorbed using
   `c^{minnorm}`. -/
set_option maxHeartbeats 1200000 in
theorem exists_ambientIntegralRowModule_projection_slab_count_of_degree_one
    {K : Type*} [Field K] [NumberField K]
    (m : ℕ) (hm : 1 < m) (hdegree : degree K = 1)
    {delta : ℝ} (hdelta : 0 < delta)
    (hmin : ∀ v : ambientIntegralRowModule (K := K) m,
      v ≠ 0 → delta ≤ ‖(v : RowVector K m)‖)
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : ambientIntegralRowModule (K := K) m), x ≠ 0 →
      ∀ {X : ℝ}, ‖(x : RowVector K m)‖ ≤ X →
        (Set.ncard {y : ambientIntegralRowModule (K := K) m |
          ‖rowAmbientProjection (K := K) (m := m)
            (x : RowVector K m) (y : RowVector K m)‖ ≤
              c * ‖(x : RowVector K m)‖ ∧
          ‖(y : RowVector K m)‖ ≤ X} : ℝ) ≤
            C * ‖(x : RowVector K m)‖ * X ^ (m - 1) := by
  let L : Submodule ℤ (RowVector K m) :=
    ambientIntegralRowModule (K := K) m
  let R : ℝ := latticeFundamentalRadius L
  let cov : ℝ := ZLattice.covolume L
    (μHE[Module.finrank ℝ (RowVector K m)] : Measure (RowVector K m))
  let U₁ : ℝ := euclideanUnitBallVolume 1
  let Uperp : ℝ := euclideanUnitBallVolume (m - 1)
  let A : ℝ := c + R / delta
  let B : ℝ := 1 + R / delta
  let C : ℝ := U₁ * Uperp * cov⁻¹ * A * B ^ (m - 1)
  have hEfin : Module.finrank ℝ (RowVector K m) = m := by
    rw [rowVector_finrank, hdegree, Nat.mul_one]
  letI : Nontrivial (RowVector K m) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hEfin]; omega)
  have hR : 0 ≤ R := latticeFundamentalRadius_nonneg L
  have hRpos : 0 < R := by
    apply latticeFundamentalRadius_pos L
  have hcov : 0 < cov := by
    dsimp [cov]
    exact ZLattice.covolume_pos L
      (μHE[Module.finrank ℝ (RowVector K m)] : Measure (RowVector K m))
  have hA : 0 < A := by
    dsimp [A]
    have : 0 < R / delta := div_pos hRpos hdelta
    linarith
  have hB : 0 < B := by
    dsimp [B]
    have : 0 < R / delta := div_pos hRpos hdelta
    linarith
  have hC : 0 < C := by
    dsimp [C, U₁, Uperp]
    exact mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (euclideanUnitBallVolume_pos 1)
            (euclideanUnitBallVolume_pos (m - 1)))
          (inv_pos.mpr hcov))
        hA)
      (pow_pos hB _)
  refine ⟨C, hC, ?_⟩
  intro x hx X hX
  let s : Submodule ℝ (RowVector K m) :=
    rowAmbientScalarLine (K := K) (m := m) (x : RowVector K m)
  have hxambient : (x : RowVector K m) ≠ 0 := by
    intro h
    apply hx
    exact Subtype.ext h
  have hsfin : Module.finrank ℝ s = 1 := by
    exact rowAmbientScalarLine_finrank_eq_one_of_degree_one hdegree hxambient
  have hsorthfin : Module.finrank ℝ sᗮ = m - 1 := by
    have hsum := s.finrank_add_finrank_orthogonal
    omega
  letI : Nontrivial s :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hsfin]; omega)
  letI : Nontrivial sᗮ :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hsorthfin]; omega)
  have hxdelta : delta ≤ ‖(x : RowVector K m)‖ := hmin x hx
  have hxnormpos : 0 < ‖(x : RowVector K m)‖ := norm_pos_iff.mpr hxambient
  have hXnonneg : 0 ≤ X := (norm_nonneg _).trans hX
  have hraw := lattice_projection_slab_count
    (L := L) (s := s) (r := c * ‖(x : RowVector K m)‖) (X := X)
    (mul_nonneg hc (norm_nonneg _)) hXnonneg
  have hradius_absorb :
      c * ‖(x : RowVector K m)‖ + R ≤ A * ‖(x : RowVector K m)‖ := by
    have hRdiv : R ≤ (R / delta) * ‖(x : RowVector K m)‖ := by
      calc
        R = (R / delta) * delta := by field_simp
        _ ≤ (R / delta) * ‖(x : RowVector K m)‖ :=
          mul_le_mul_of_nonneg_left hxdelta (div_nonneg hR hdelta.le)
    dsimp [A]
    nlinarith
  have hXradius_absorb : X + R ≤ B * X := by
    have hdeltaX : delta ≤ X := hxdelta.trans hX
    have hRdiv : R ≤ (R / delta) * X := by
      calc
        R = (R / delta) * delta := by field_simp
        _ ≤ (R / delta) * X :=
          mul_le_mul_of_nonneg_left hdeltaX (div_nonneg hR hdelta.le)
    dsimp [B]
    nlinarith
  have hpow : (X + R) ^ (m - 1) ≤ (B * X) ^ (m - 1) :=
    pow_le_pow_left₀ (add_nonneg hXnonneg hR) hXradius_absorb _
  have hraw' :
      (Set.ncard {y : L |
        ‖s.starProjection (y : RowVector K m)‖ ≤
            c * ‖(x : RowVector K m)‖ ∧
          ‖(y : RowVector K m)‖ ≤ X} : ℝ) ≤
        ((c * ‖(x : RowVector K m)‖ + R) * U₁ *
          ((X + R) ^ (m - 1) * Uperp)) * cov⁻¹ := by
    simpa [L, R, cov, U₁, Uperp, hsfin, hsorthfin] using hraw
  have hgeom :
      ((c * ‖(x : RowVector K m)‖ + R) * U₁ *
          ((X + R) ^ (m - 1) * Uperp)) * cov⁻¹ ≤
        C * ‖(x : RowVector K m)‖ * X ^ (m - 1) := by
    have hU₁ : 0 ≤ U₁ := (euclideanUnitBallVolume_pos 1).le
    have hUperp : 0 ≤ Uperp := (euclideanUnitBallVolume_pos (m - 1)).le
    have hcovinv : 0 ≤ cov⁻¹ := inv_nonneg.mpr hcov.le
    calc
      ((c * ‖(x : RowVector K m)‖ + R) * U₁ *
          ((X + R) ^ (m - 1) * Uperp)) * cov⁻¹ ≤
          (A * ‖(x : RowVector K m)‖) * U₁ *
            ((B * X) ^ (m - 1) * Uperp) * cov⁻¹ := by
        gcongr
      _ = C * ‖(x : RowVector K m)‖ * X ^ (m - 1) := by
        dsimp [C]
        rw [mul_pow]
        ring
  change (Set.ncard {y : L |
    ‖rowAmbientProjection (K := K) (m := m)
      (x : RowVector K m) (y : RowVector K m)‖ ≤
        c * ‖(x : RowVector K m)‖ ∧
      ‖(y : RowVector K m)‖ ≤ X} : ℝ) ≤
        C * ‖(x : RowVector K m)‖ * X ^ (m - 1)
  calc
    (Set.ncard {y : L |
      ‖rowAmbientProjection (K := K) (m := m)
        (x : RowVector K m) (y : RowVector K m)‖ ≤
          c * ‖(x : RowVector K m)‖ ∧
        ‖(y : RowVector K m)‖ ≤ X} : ℝ) =
      (Set.ncard {y : L |
        ‖s.starProjection (y : RowVector K m)‖ ≤
            c * ‖(x : RowVector K m)‖ ∧
          ‖(y : RowVector K m)‖ ≤ X} : ℝ) := by
        rfl
    _ ≤ ((c * ‖(x : RowVector K m)‖ + R) * U₁ *
          ((X + R) ^ (m - 1) * Uperp)) * cov⁻¹ := hraw'
    _ ≤ C * ‖(x : RowVector K m)‖ * X ^ (m - 1) := hgeom

end Katznelson
