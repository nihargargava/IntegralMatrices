import Katznelson.Counting.RiemannSum

/-!
# Riemann sums controlled by an ambient oscillation

For a function restricted to a real subspace, the paper bounds its cellwise
oscillation by the ambient error function E_f; it does not replace E_f
by a supremum taken only inside the subspace.  This file isolates exactly the
data used in the proof of Lemma le:Riemann_estimate.
-/

namespace Katznelson

open MeasureTheory Set Module
open scoped Classical MeasureTheory Pointwise

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/- [Lean infrastructure for paper `re:help`, lines 550--562] The hypotheses
   actually used by the lattice Riemann-sum proof, with an explicit upper
   range for the error-function parameter.  Omitting `εMax` means the
   manuscript's original range `0 < ε ≤ 1`; a separately proved update of
   the error control may instantiate a larger fixed range. -/
structure RiemannControl (f : E → ℝ) (εMax : ℝ := 1) where
  oscillation : E → ℝ → ℝ
  compactSupport : HasCompactSupport f
  integrable : Integrable f
    (μHE[Module.finrank ℝ E] : Measure E)
  oscillation_nonneg :
    ∀ x ε, 0 ≤ ε → 0 ≤ oscillation x ε
  abs_sub_le :
    ∀ {x y ε}, dist x y ≤ ε → |f x - f y| ≤ oscillation x ε
  oscillation_integrable :
    ∀ ε, 0 < ε → ε ≤ εMax →
      Integrable (fun x => oscillation x ε)
        (μHE[Module.finrank ℝ E] : Measure E)
  oscillation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ε, 0 < ε → ε ≤ εMax →
      ∫ x : E, oscillation x ε
        ∂(μHE[Module.finrank ℝ E] : Measure E) ≤ C * ε

/- [Lean infrastructure for paper `re:help`, lines 550--562] Replace only
   the proved range of a fixed ambient oscillation control.  The two supplied
   hypotheses are exactly the analytic content of the manuscript's phrase
   "suitably updating the constant"; this definition does not assert that
   they follow automatically from the original `ε ≤ 1` control. -/
def RiemannControl.withUpdatedRange
    {f : E → ℝ} {εOld εMax : ℝ} (h : RiemannControl f εOld)
    (hIntegrable : ∀ ε, 0 < ε → ε ≤ εMax →
      Integrable (fun x => h.oscillation x ε)
        (μHE[Module.finrank ℝ E] : Measure E))
    (hBound : ∃ C : ℝ, 0 < C ∧ ∀ ε, 0 < ε → ε ≤ εMax →
      ∫ x : E, h.oscillation x ε
        ∂(μHE[Module.finrank ℝ E] : Measure E) ≤ C * ε) :
    RiemannControl f εMax where
  oscillation := h.oscillation
  compactSupport := h.compactSupport
  integrable := h.integrable
  oscillation_nonneg := h.oscillation_nonneg
  abs_sub_le := h.abs_sub_le
  oscillation_integrable := hIntegrable
  oscillation_bound := hBound

variable [Nontrivial E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

omit [Nontrivial E] in
theorem RiemannControl.scaled_oscillation_integrable
    {f : E → ℝ} {εMax : ℝ} (h : RiemannControl f εMax) {T ε : ℝ}
    (hT : 0 < T) (hε : 0 < ε) (hεMax : ε ≤ εMax) :
    Integrable (fun x : E => h.oscillation (T⁻¹ • x) ε)
      (μHE[Module.finrank ℝ E] : Measure E) := by
  exact (h.oscillation_integrable ε hε hεMax).comp_smul
    (inv_ne_zero hT.ne')

theorem controlled_cell_integral_error_bound
    (f : E → ℝ) {εMax : ℝ} (h : RiemannControl f εMax)
    {T : ℝ} (hT : 0 < T) (v : L)
    (hRadius : latticeFundamentalRadius L / T ≤ εMax) :
    |∫ x in latticeFundamentalDomain L,
        (f (T⁻¹ • (v : E)) - f (T⁻¹ • ((v : E) + x)))
        ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
      ∫ x in latticeFundamentalDomain L,
        h.oscillation (T⁻¹ • ((v : E) + x))
          (latticeFundamentalRadius L / T)
        ∂(μHE[Module.finrank ℝ E] : Measure E) := by
  let mu : Measure E := (μHE[Module.finrank ℝ E] : Measure E)
  let ε : ℝ := latticeFundamentalRadius L / T
  have hε : 0 < ε := div_pos (latticeFundamentalRadius_pos L) hT
  have hbase : Integrable
      (fun x : E => h.oscillation (T⁻¹ • x) ε) mu :=
    h.scaled_oscillation_integrable hT hε hRadius
  have htranslated : Integrable
      (fun x : E => h.oscillation (T⁻¹ • ((v : E) + x)) ε) mu := by
    have hmp := measurePreserving_add_left mu (v : E)
    simpa [Function.comp_def] using hmp.integrable_comp_of_integrable hbase
  have hF : MeasurableSet (latticeFundamentalDomain L) :=
    ZSpan.fundamentalDomain_measurableSet (latticeRealBasis L)
  rw [← Real.norm_eq_abs]
  change ‖∫ x in latticeFundamentalDomain L,
      (f (T⁻¹ • (v : E)) - f (T⁻¹ • ((v : E) + x))) ∂mu‖ ≤
    ∫ x in latticeFundamentalDomain L,
      h.oscillation (T⁻¹ • ((v : E) + x)) ε ∂mu
  apply norm_integral_le_of_norm_le htranslated.restrict
  filter_upwards [ae_restrict_mem hF] with x hx
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact h.abs_sub_le (dist_scaled_add_latticePoint_le L hT v hx)

theorem controlled_tsum_cell_integral_error_bound
    (f : E → ℝ) {εMax : ℝ} (h : RiemannControl f εMax)
    {T : ℝ} (hT : 0 < T)
    (hRadius : latticeFundamentalRadius L / T ≤ εMax) :
    |∑' v : L, ∫ x in latticeFundamentalDomain L,
        (f (T⁻¹ • (v : E)) - f (T⁻¹ • ((v : E) + x)))
        ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
      ∫ x : E, h.oscillation (T⁻¹ • x)
        (latticeFundamentalRadius L / T)
        ∂(μHE[Module.finrank ℝ E] : Measure E) := by
  let mu : Measure E := (μHE[Module.finrank ℝ E] : Measure E)
  let _ : VAddInvariantMeasure L E mu :=
    ⟨fun v s _ => by
      change mu ((fun x : E => (v : E) + x) ⁻¹' s) = mu s
      exact measure_preimage_add mu (v : E) s⟩
  let F : Set E := latticeFundamentalDomain L
  let ε : ℝ := latticeFundamentalRadius L / T
  let g : E → ℝ := fun x => h.oscillation (T⁻¹ • x) ε
  let a : L → ℝ := fun v =>
    ∫ x in F, f (T⁻¹ • (v : E)) - f (T⁻¹ • ((v : E) + x)) ∂mu
  let b : L → ℝ := fun v => ∫ x in F, g ((v : E) + x) ∂mu
  have hε : 0 < ε := div_pos (latticeFundamentalRadius_pos L) hT
  have hbase : Integrable g mu :=
    h.scaled_oscillation_integrable hT hε hRadius
  have hfund : IsAddFundamentalDomain L F mu :=
    latticeFundamentalDomain_isAddFundamentalDomain L mu
  have hsumIntegrable : Integrable g
      (Measure.sum fun v : L => mu.restrict (v +ᵥ F)) := by
    rw [hfund.sum_restrict]
    exact hbase
  have hnormg : (fun x : E => ‖g x‖) = g := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact h.oscillation_nonneg _ _ hε.le
  have hb : Summable b := by
    refine hsumIntegrable.summable_integral.congr (fun v => ?_)
    change (∫ x in v +ᵥ F, ‖g x‖ ∂mu) = b v
    rw [hnormg]
    exact integral_vadd_latticeFundamentalDomain L g v
  have hba : ∀ v, ‖a v‖ ≤ b v := by
    intro v
    dsimp only [a, b, g, F, ε, mu]
    rw [Real.norm_eq_abs]
    exact controlled_cell_integral_error_bound L f h hT v hRadius
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

theorem controlled_covolume_mul_latticeSum_sub_integral_le
    (f : E → ℝ) {εMax : ℝ} (h : RiemannControl f εMax)
    {T : ℝ} (hT : 0 < T)
    (hRadius : latticeFundamentalRadius L / T ≤ εMax) :
    |ZLattice.covolume L
          (μHE[Module.finrank ℝ E] : Measure E) *
        (∑' v : L, f (T⁻¹ • (v : E))) -
        ∫ x : E, f (T⁻¹ • x)
          ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
      ∫ x : E, h.oscillation (T⁻¹ • x)
        (latticeFundamentalRadius L / T)
        ∂(μHE[Module.finrank ℝ E] : Measure E) := by
  let mu : Measure E := (μHE[Module.finrank ℝ E] : Measure E)
  let _ : VAddInvariantMeasure L E mu :=
    ⟨fun v s _ => by
      change mu ((fun x : E => (v : E) + x) ⁻¹' s) = mu s
      exact measure_preimage_add mu (v : E) s⟩
  let F : Set E := latticeFundamentalDomain L
  let C : ℝ := ZLattice.covolume L mu
  let scaled : E → ℝ := fun x => f (T⁻¹ • x)
  let cellIntegral : L → ℝ := fun v =>
    ∫ x in F, scaled ((v : E) + x) ∂mu
  let cellError : L → ℝ := fun v =>
    ∫ x in F, scaled (v : E) - scaled ((v : E) + x) ∂mu
  have hscaled : Integrable scaled mu :=
    h.integrable.comp_smul (inv_ne_zero hT.ne')
  have hlattice : Summable (fun v : L => scaled (v : E)) :=
    summable_scaled_lattice_of_hasCompactSupport L f h.compactSupport hT
  have hcells : Summable cellIntegral :=
    summable_integral_latticeFundamentalDomain L scaled hscaled
  have hFfinite : mu F ≠ ⊤ :=
    ne_of_lt (latticeFundamentalDomain_isBounded L).measure_lt_top
  have hcellError (v : L) :
      cellError v = C * scaled (v : E) - cellIntegral v := by
    have htranslated : Integrable (fun x : E => scaled ((v : E) + x)) mu := by
      have hmp := measurePreserving_add_left mu (v : E)
      simpa [Function.comp_def] using hmp.integrable_comp_of_integrable hscaled
    have hconst : IntegrableOn (fun _ : E => scaled (v : E)) F mu :=
      integrableOn_const hFfinite
    dsimp only [cellError, cellIntegral]
    rw [integral_sub hconst htranslated.restrict, setIntegral_const, smul_eq_mul]
    change mu.real F * scaled (v : E) -
        (∫ x in F, scaled ((v : E) + x) ∂mu) =
      C * scaled (v : E) -
        ∫ x in F, scaled ((v : E) + x) ∂mu
    rw [← covolume_eq_measureReal_latticeFundamentalDomain L mu]
  have hfund : IsAddFundamentalDomain L F mu :=
    latticeFundamentalDomain_isAddFundamentalDomain L mu
  have hintegral : ∫ x : E, scaled x ∂mu = ∑' v, cellIntegral v := by
    rw [hfund.integral_eq_tsum'' scaled hscaled]
    apply tsum_congr
    intro v
    apply integral_congr_ae
    filter_upwards with x
    rfl
  have hidentity :
      C * (∑' v : L, scaled (v : E)) - ∫ x : E, scaled x ∂mu =
        ∑' v, cellError v := by
    calc
      C * (∑' v : L, scaled (v : E)) - ∫ x : E, scaled x ∂mu =
          (∑' v : L, C * scaled (v : E)) - ∑' v, cellIntegral v := by
        rw [tsum_mul_left, hintegral]
      _ = ∑' v : L, (C * scaled (v : E) - cellIntegral v) :=
        ((hlattice.mul_left C).tsum_sub hcells).symm
      _ = ∑' v, cellError v := by
        apply tsum_congr
        intro v
        exact (hcellError v).symm
  change |C * (∑' v : L, scaled (v : E)) -
      ∫ x : E, scaled x ∂mu| ≤
    ∫ x : E, h.oscillation (T⁻¹ • x)
      (latticeFundamentalRadius L / T) ∂mu
  rw [hidentity]
  exact controlled_tsum_cell_integral_error_bound L f h hT hRadius

theorem controlled_latticeRiemann_estimate_weighted
    (f : E → ℝ) {εMax : ℝ} (h : RiemannControl f εMax) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      latticeFundamentalRadius L / T ≤ εMax →
      |ZLattice.covolume L
            (μHE[Module.finrank ℝ E] : Measure E) *
          ((∑' v : L, f (T⁻¹ • (v : E))) /
            T ^ Module.finrank ℝ E) -
          ∫ x : E, f x
            ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
        Cₐ * latticeFundamentalRadius L / T := by
  obtain ⟨Cₐ, hCₐ, herror⟩ := h.oscillation_bound
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  let q : ℕ := Module.finrank ℝ E
  let scale : ℝ := T ^ q
  let covol : ℝ := ZLattice.covolume L
    (μHE[Module.finrank ℝ E] : Measure E)
  let latticeSum : ℝ := ∑' v : L, f (T⁻¹ • (v : E))
  let ambientIntegral : ℝ :=
    ∫ x : E, f x ∂(μHE[Module.finrank ℝ E] : Measure E)
  let ε : ℝ := latticeFundamentalRadius L / T
  have hε : 0 < ε := div_pos (latticeFundamentalRadius_pos L) hT
  have hscale : 0 < scale := pow_pos hT q
  have hraw := controlled_covolume_mul_latticeSum_sub_integral_le
    L f h hT hRadius
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
  change |covol * (latticeSum / scale) - ambientIntegral| ≤
    Cₐ * latticeFundamentalRadius L / T
  rw [hidentity, abs_div, abs_of_pos hscale]
  apply (div_le_iff₀ hscale).2
  simpa [ε, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hraw'

theorem controlled_latticeRiemann_estimate
    (f : E → ℝ) {εMax : ℝ} (h : RiemannControl f εMax) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      latticeFundamentalRadius L / T ≤ εMax →
      |(∑' v : L, f (T⁻¹ • (v : E))) /
            T ^ Module.finrank ℝ E -
          (ZLattice.covolume L
            (μHE[Module.finrank ℝ E] : Measure E))⁻¹ *
            ∫ x : E, f x
              ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
        Cₐ * latticeFundamentalRadius L /
          (ZLattice.covolume L
            (μHE[Module.finrank ℝ E] : Measure E) * T) := by
  obtain ⟨Cₐ, hCₐ, hweighted⟩ :=
    controlled_latticeRiemann_estimate_weighted L f h
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  let covol : ℝ := ZLattice.covolume L
    (μHE[Module.finrank ℝ E] : Measure E)
  let latticeAverage : ℝ :=
    (∑' v : L, f (T⁻¹ • (v : E))) / T ^ Module.finrank ℝ E
  let ambientIntegral : ℝ :=
    ∫ x : E, f x ∂(μHE[Module.finrank ℝ E] : Measure E)
  have hcovol : 0 < covol :=
    ZLattice.covolume_pos L
      (μHE[Module.finrank ℝ E] : Measure E)
  have hbound := hweighted T hT hRadius
  change |covol * latticeAverage - ambientIntegral| ≤
    Cₐ * latticeFundamentalRadius L / T at hbound
  have hidentity :
      latticeAverage - covol⁻¹ * ambientIntegral =
        (covol * latticeAverage - ambientIntegral) / covol := by
    field_simp [hcovol.ne']
  have hrhs :
      Cₐ * latticeFundamentalRadius L / (covol * T) =
        (Cₐ * latticeFundamentalRadius L / T) / covol := by
    field_simp [hcovol.ne', hT.ne']
  change |latticeAverage - covol⁻¹ * ambientIntegral| ≤
    Cₐ * latticeFundamentalRadius L / (covol * T)
  rw [hidentity, abs_div, abs_of_pos hcovol, hrhs]
  exact (div_le_div_iff_of_pos_right hcovol).2 hbound

end

end Katznelson
