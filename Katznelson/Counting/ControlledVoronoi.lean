import Katznelson.Counting.ControlledRiemann

/-!
# Voronoi Riemann sums with ambient oscillation control

This module supplies the manuscript-facing Voronoi-cell version of the
controlled Riemann-sum argument.  In particular, a restriction of an
admissible ambient function keeps its ambient error function, as required by
`hy:admissible`; it is not replaced by a new subspace supremum.
-/

namespace Katznelson

open MeasureTheory Set Module
open scoped Classical MeasureTheory Pointwise

section ControlledFundamentalDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/- [derived consequence, paper `le:Riemann_estimate`, lines 582--607] The
   cellwise estimate for an arbitrary bounded fundamental domain, retaining
   the ambient oscillation supplied by `RiemannControl`. -/
theorem controlled_cell_integral_error_bound_fundamentalDomain
    (F : Set E) (R : ℝ) (hF : MeasurableSet F)
    (hFbound : ∀ x : E, x ∈ F → ‖x‖ ≤ R) (hRpos : 0 < R)
    (f : E → ℝ) {εMax : ℝ} (h : RiemannControl f εMax) {T : ℝ} (hT : 0 < T)
    (v : L) (hRadius : R / T ≤ εMax) :
    |∫ x in F, (f (T⁻¹ • (v : E)) - f (T⁻¹ • ((v : E) + x)))
        ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
      ∫ x in F, h.oscillation (T⁻¹ • ((v : E) + x)) (R / T)
        ∂(μHE[Module.finrank ℝ E] : Measure E) := by
  let mu : Measure E := (μHE[Module.finrank ℝ E] : Measure E)
  let ε := R / T
  have hε : 0 < ε := div_pos hRpos hT
  have hbase : Integrable
      (fun x : E => h.oscillation (T⁻¹ • x) ε) mu := by
    exact h.scaled_oscillation_integrable hT hε hRadius
  have htranslated : Integrable
      (fun x : E => h.oscillation (T⁻¹ • ((v : E) + x)) ε) mu := by
    have hmp := measurePreserving_add_left mu (v : E)
    simpa [Function.comp_def] using hmp.integrable_comp_of_integrable hbase
  rw [← Real.norm_eq_abs]
  change ‖∫ x in F,
      (f (T⁻¹ • (v : E)) - f (T⁻¹ • ((v : E) + x))) ∂mu‖ ≤
    ∫ x in F, h.oscillation (T⁻¹ • ((v : E) + x)) ε ∂mu
  apply norm_integral_le_of_norm_le htranslated.restrict
  filter_upwards [ae_restrict_mem hF] with x hx
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact h.abs_sub_le
    (dist_scaled_add_fundamentalDomain_le L F R hFbound hT v hx)

/- [derived consequence, paper `le:Riemann_estimate`, lines 582--607] Sum
   the controlled cellwise errors over a fundamental-domain tiling. -/
theorem controlled_tsum_cell_integral_error_bound_fundamentalDomain
    (F : Set E) (R : ℝ) (hF : MeasurableSet F)
    (hfund : IsAddFundamentalDomain L F
      (μHE[Module.finrank ℝ E] : Measure E))
    (hFbound : ∀ x : E, x ∈ F → ‖x‖ ≤ R) (hRpos : 0 < R)
    (f : E → ℝ) {εMax : ℝ} (h : RiemannControl f εMax) {T : ℝ} (hT : 0 < T)
    (hRadius : R / T ≤ εMax) :
    |∑' v : L, ∫ x in F,
        (f (T⁻¹ • (v : E)) - f (T⁻¹ • ((v : E) + x)))
        ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
      ∫ x : E, h.oscillation (T⁻¹ • x) (R / T)
        ∂(μHE[Module.finrank ℝ E] : Measure E) := by
  let mu : Measure E := (μHE[Module.finrank ℝ E] : Measure E)
  change IsAddFundamentalDomain L F mu at hfund
  let ε : ℝ := R / T
  let g : E → ℝ := fun x => h.oscillation (T⁻¹ • x) ε
  let a : L → ℝ := fun v =>
    ∫ x in F, f (T⁻¹ • (v : E)) - f (T⁻¹ • ((v : E) + x) ) ∂mu
  let b : L → ℝ := fun v => ∫ x in F, g ((v : E) + x) ∂mu
  have hε : 0 < ε := div_pos hRpos hT
  have hbase : Integrable g mu := by
    exact h.scaled_oscillation_integrable hT hε hRadius
  let _ : VAddInvariantMeasure L E mu :=
    ⟨fun v s _ => by
      change mu ((fun x : E => (v : E) + x) ⁻¹' s) = mu s
      exact measure_preimage_add mu (v : E) s⟩
  have hsumIntegrable : Integrable g
      (Measure.sum fun v : L => mu.restrict (v +ᵥ F)) := by
    rw [hfund.sum_restrict]
    exact hbase
  have hnormg : (fun x : E => ‖g x‖) = g := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact h.oscillation_nonneg _ _ hε.le
  have hb : Summable b := by
    have hb' := hsumIntegrable.summable_integral
    refine hb'.congr (fun v => ?_)
    change (∫ x in v +ᵥ F, ‖g x‖ ∂mu) = b v
    rw [hnormg]
    exact integral_vadd_fundamentalDomain L F g v
  have hba : ∀ v, ‖a v‖ ≤ b v := by
    intro v
    dsimp only [a, b, g, ε, mu]
    rw [Real.norm_eq_abs]
    exact controlled_cell_integral_error_bound_fundamentalDomain
      L F R hF hFbound hRpos f h hT v hRadius
  have haNorm : Summable (fun v => ‖a v‖) :=
    hb.of_nonneg_of_le (fun v => norm_nonneg (a v)) hba
  have hb_tsum : ∑' v, b v = ∫ x : E, g x ∂mu := by
    calc
      ∑' v, b v = ∑' v : L, ∫ x in F, g (v +ᵥ x) ∂mu := by
        apply tsum_congr
        intro v
        rfl
      _ = ∫ x : E, g x ∂mu :=
        (hfund.integral_eq_tsum'' g hbase).symm
  change |∑' v, a v| ≤ ∫ x : E, g x ∂mu
  rw [← Real.norm_eq_abs]
  calc
    ‖∑' v, a v‖ ≤ ∑' v, ‖a v‖ := norm_tsum_le_tsum_norm haNorm
    _ ≤ ∑' v, b v := haNorm.tsum_le_tsum hba hb
    _ = ∫ x : E, g x ∂mu := hb_tsum

/- [derived consequence, paper `le:Riemann_estimate`, lines 582--607] The
   summed cell error is the covolume-weighted lattice sum minus the scaled
   integral, with the same ambient oscillation control. -/
theorem controlled_covolume_mul_latticeSum_sub_integral_le_fundamentalDomain
    (F : Set E) (R : ℝ) (hF : MeasurableSet F)
    (hfund : IsAddFundamentalDomain L F
      (μHE[Module.finrank ℝ E] : Measure E))
    (hFbound : ∀ x : E, x ∈ F → ‖x‖ ≤ R) (hRpos : 0 < R)
    (f : E → ℝ) {εMax : ℝ} (h : RiemannControl f εMax) {T : ℝ} (hT : 0 < T)
    (hRadius : R / T ≤ εMax) :
    |ZLattice.covolume L
          (μHE[Module.finrank ℝ E] : Measure E) *
        (∑' v : L, f (T⁻¹ • (v : E))) -
        ∫ x : E, f (T⁻¹ • x)
          ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
      ∫ x : E, h.oscillation (T⁻¹ • x) (R / T)
        ∂(μHE[Module.finrank ℝ E] : Measure E) := by
  let mu : Measure E := (μHE[Module.finrank ℝ E] : Measure E)
  change IsAddFundamentalDomain L F mu at hfund
  let scaled : E → ℝ := fun x => f (T⁻¹ • x)
  let cellIntegral : L → ℝ := fun v =>
    ∫ x in F, scaled ((v : E) + x) ∂mu
  let cellError : L → ℝ := fun v =>
    ∫ x in F, scaled (v : E) - scaled ((v : E) + x) ∂mu
  let _ : VAddInvariantMeasure L E mu :=
    ⟨fun v s _ => by
      change mu ((fun x : E => (v : E) + x) ⁻¹' s) = mu s
      exact measure_preimage_add mu (v : E) s⟩
  have hscaled : Integrable scaled mu :=
    h.integrable.comp_smul (inv_ne_zero hT.ne')
  have hlattice : Summable (fun v : L => scaled (v : E)) := by
    exact summable_scaled_lattice_of_hasCompactSupport L f h.compactSupport hT
  have hcells : Summable cellIntegral := by
    exact summable_integral_fundamentalDomain L F hfund scaled hscaled
  have hFbounded : Bornology.IsBounded F := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : E)]
    refine ⟨R, ?_⟩
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hFbound x hx
  have hFfinite : mu F ≠ ⊤ := by
    exact ne_of_lt hFbounded.measure_lt_top
  have hcellError (v : L) :
      cellError v = ZLattice.covolume L mu * scaled (v : E) - cellIntegral v := by
    have htranslated : Integrable (fun x : E => scaled ((v : E) + x)) mu := by
      have hmp := measurePreserving_add_left mu (v : E)
      simpa [Function.comp_def] using hmp.integrable_comp_of_integrable hscaled
    have hconst : IntegrableOn (fun _ : E => scaled (v : E)) F mu :=
      integrableOn_const hFfinite
    dsimp only [cellError, cellIntegral]
    rw [integral_sub hconst htranslated.restrict,
      setIntegral_const, smul_eq_mul]
    change mu.real F * scaled (v : E) -
        (∫ x in F, scaled ((v : E) + x) ∂mu) =
      ZLattice.covolume L mu * scaled (v : E) -
        ∫ x in F, scaled ((v : E) + x) ∂mu
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L mu hfund]
  have hintegral : ∫ x : E, scaled x ∂mu = ∑' v, cellIntegral v := by
    rw [hfund.integral_eq_tsum'' scaled hscaled]
    apply tsum_congr
    intro v
    apply integral_congr_ae
    filter_upwards with x
    rfl
  have hidentity :
      ZLattice.covolume L mu * (∑' v : L, scaled (v : E)) -
          ∫ x : E, scaled x ∂mu =
        ∑' v, cellError v := by
    calc
      ZLattice.covolume L mu * (∑' v : L, scaled (v : E)) -
            ∫ x : E, scaled x ∂mu =
          (∑' v : L, ZLattice.covolume L mu * scaled (v : E)) -
            ∑' v, cellIntegral v := by
        rw [tsum_mul_left, hintegral]
      _ = ∑' v : L,
          (ZLattice.covolume L mu * scaled (v : E) - cellIntegral v) :=
        ((hlattice.mul_left _).tsum_sub hcells).symm
      _ = ∑' v, cellError v := by
        apply tsum_congr
        intro v
        exact (hcellError v).symm
  change |ZLattice.covolume L mu * (∑' v : L, scaled (v : E)) -
      ∫ x : E, scaled x ∂mu| ≤
    ∫ x : E, h.oscillation (T⁻¹ • x) (R / T) ∂mu
  rw [hidentity]
  exact controlled_tsum_cell_integral_error_bound_fundamentalDomain
    L F R hF hfund hFbound hRpos f h hT hRadius

/- [derived consequence, paper `le:Riemann_estimate`, lines 574--607] The
   normalized Riemann estimate for a controlled function and any bounded
   fundamental domain. -/
theorem controlled_latticeRiemann_estimate_of_fundamentalDomain
    (F : Set E) (R : ℝ) (hF : MeasurableSet F)
    (hfund : IsAddFundamentalDomain L F
      (μHE[Module.finrank ℝ E] : Measure E))
    (hFbound : ∀ x : E, x ∈ F → ‖x‖ ≤ R) (hRpos : 0 < R)
    (f : E → ℝ) {εMax : ℝ} (h : RiemannControl f εMax) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      R / T ≤ εMax →
      |(∑' v : L, f (T⁻¹ • (v : E))) /
            T ^ Module.finrank ℝ E -
          (ZLattice.covolume L
            (μHE[Module.finrank ℝ E] : Measure E))⁻¹ *
            ∫ x : E, f x
              ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
        Cₐ * R /
          (ZLattice.covolume L
            (μHE[Module.finrank ℝ E] : Measure E) * T) := by
  obtain ⟨Cₐ, hCₐ, herror⟩ := h.oscillation_bound
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
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
  have hraw := controlled_covolume_mul_latticeSum_sub_integral_le_fundamentalDomain
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

end ControlledFundamentalDomain

section ControlledIntrinsicVoronoi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [ProperSpace E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/- [derived consequence of paper `le:Riemann_estimate`, lines 574--607, and
   `re:help`, lines 550--562] The manuscript-facing Riemann estimate for a
   supplied error control valid through `εMax`: the Voronoi fundamental domain
   gives the intrinsic covering radius `ρ`, while `RiemannControl` preserves
   the ambient error function.  The default `εMax = 1` is the original
   admissibility hypothesis; the paper's arbitrary constant is represented
   only after its updated control has been supplied. -/
theorem controlled_latticeVoronoiRiemann_estimate
    (f : E → ℝ) {εMax : ℝ} (h : RiemannControl f εMax) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      latticeCoveringRadius L / T ≤ εMax →
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
  have hF : MeasurableSet F := by
    exact isClosed_latticeVoronoiDomain L |>.measurableSet
  have hfund : IsAddFundamentalDomain L F
      (μHE[Module.finrank ℝ E] : Measure E) := by
    exact latticeVoronoiDomain_isAddFundamentalDomain L
      (μHE[Module.finrank ℝ E] : Measure E)
  have hFbound : ∀ x : E, x ∈ F → ‖x‖ ≤ latticeCoveringRadius L := by
    intro x hx
    exact norm_le_latticeCoveringRadius_of_mem_latticeVoronoiDomain L hx
  exact controlled_latticeRiemann_estimate_of_fundamentalDomain L F
    (latticeCoveringRadius L) hF hfund hFbound (latticeCoveringRadius_pos L) f h

end ControlledIntrinsicVoronoi

end Katznelson
