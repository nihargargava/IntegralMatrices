import Katznelson.Counting.ControlledRiemann

/-!
# Riemann sums on real subspaces

This file specializes the controlled lattice Riemann estimate to the
restriction of an admissible ambient function to a nonzero real subspace.
The controlling oscillation is the paper's ambient error function `E_f`,
restricted to the subspace, exactly as in Hypothesis `hy:admissible` and
Lemma `le:Riemann_estimate` of `papers/katznelson.tex`.
-/

namespace Katznelson

open MeasureTheory Set Module
open scoped Classical MeasureTheory Pointwise

section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]

/-- Restrict an admissible function to a nonzero subspace while retaining
the ambient error function as its oscillation control. -/
noncomputable def Admissible.submoduleRiemannControl
    {f : X → ℝ} (h_f : Admissible f) (V : Submodule ℝ X) (hV : V ≠ ⊥) :
    RiemannControl (fun x : V => f x) where
  oscillation := fun x ε => errorFunction f (x : X) ε
  compactSupport := by
    simpa [Function.comp_def] using
      h_f.compactSupport.comp_isClosedEmbedding
        V.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal
  integrable := by
    let μ : Measure V := μHE[Module.finrank ℝ V]
    let K : Set V := (Subtype.val : V → X) ⁻¹' tsupport f
    have hK : IsCompact K :=
      V.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isCompact_preimage
        h_f.compactSupport
    have hKfinite : μ K ≠ ⊤ := ne_of_lt hK.measure_lt_top
    have hfMeasurable : Measurable f :=
      (isBorelMeasurable_iff f).mp h_f.measurable
    have hrestrictedMeasurable : Measurable (fun x : V => f x) :=
      hfMeasurable.comp continuous_subtype_val.measurable
    obtain ⟨C, hC⟩ := h_f.bounded.subset_closedBall (0 : ℝ)
    have hbounded : ∀ x : V, ‖f x‖ ≤ max C 0 := by
      intro x
      have hx := hC ⟨(x : X), rfl⟩
      have hx' : |f x| ≤ C := by
        simpa [dist_comm, Real.dist_0_eq_abs] using hx
      rw [Real.norm_eq_abs]
      exact hx'.trans (le_max_left _ _)
    have hIntegrableOn : IntegrableOn (fun x : V => f x) K μ :=
      μ.integrableOn_of_bounded hKfinite
        hrestrictedMeasurable.aestronglyMeasurable
        (ae_of_all _ hbounded)
    have hsupport : Function.support (fun x : V => f x) ⊆ K := by
      intro x hx
      change (x : X) ∈ tsupport f
      exact subset_closure hx
    exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hIntegrableOn
  oscillation_nonneg := by
    intro x ε hε
    exact h_f.errorFunction_nonneg hε
  abs_sub_le := by
    intro x y ε hxy
    exact h_f.abs_sub_le_errorFunction hxy
  oscillation_integrable := by
    intro ε hε hεone
    exact (euclideanIntegrable_iff _).mp
      (h_f.error_integrable V hV ε hε hεone)
  oscillation_bound := by
    obtain ⟨C, hC, hbound⟩ := h_f.error_bound
    refine ⟨C, hC, fun ε hε hεone => ?_⟩
    rw [← euclideanIntegral_eq_integral]
    exact hbound V hV ε hε hεone

/-- Lemma `le:Riemann_estimate` applied to an arbitrary full lattice in a
nonzero real subspace. -/
theorem Admissible.submodule_latticeRiemann_estimate
    {f : X → ℝ} (h_f : Admissible f) (V : Submodule ℝ X) (hV : V ≠ ⊥)
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      latticeFundamentalRadius L / T ≤ 1 →
      |(∑' v : L, f (T⁻¹ • (v : V) : V)) /
            T ^ Module.finrank ℝ V -
          (ZLattice.covolume L
            (μHE[Module.finrank ℝ V] : Measure V))⁻¹ *
            ∫ x : V, f x
              ∂(μHE[Module.finrank ℝ V] : Measure V)| ≤
        Cₐ * latticeFundamentalRadius L /
          (ZLattice.covolume L
            (μHE[Module.finrank ℝ V] : Measure V) * T) := by
  letI : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV
  exact controlled_latticeRiemann_estimate L (fun x : V => f x)
    (h_f.submoduleRiemannControl V hV)

end

end Katznelson
