import Katznelson.Counting.RankDrop
import Katznelson.Counting.Admissible
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Compact support and finiteness of lattice sums

This file supplies the finiteness facts used implicitly whenever the paper
rewrites a compactly supported sum over integral matrices.  In particular,
all `tsum`s occurring at a positive scale have finite support.
-/

namespace Katznelson

open MeasureTheory Set
open scoped Classical NumberField

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

section Admissible

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

omit [FiniteDimensional ℝ X] in
theorem Admissible.exists_support_radius {f : X → ℝ} (h_f : Admissible f) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x, f x ≠ 0 → ‖x‖ ≤ R := by
  obtain ⟨R, hR⟩ := h_f.compactSupport.isBounded.subset_closedBall (0 : X)
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  have hxsupport : x ∈ Function.support f := hx
  have hxtsupport : x ∈ tsupport f := subset_closure hxsupport
  have hxball := hR hxtsupport
  rw [Metric.mem_closedBall, dist_zero_right] at hxball
  exact hxball.trans (le_max_left _ _)

omit [FiniteDimensional ℝ X] in
theorem Admissible.exists_uniform_bound {f : X → ℝ} (h_f : Admissible f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := h_f.bounded.subset_closedBall (0 : ℝ)
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hx := hC ⟨x, rfl⟩
  rw [Metric.mem_closedBall, Real.dist_0_eq_abs] at hx
  exact hx.trans (le_max_left _ _)

end Admissible

section IntegralPoints

variable {K : Type*} [Field K] [NumberField K]

theorem finite_integralElements_norm_le (R : ℝ) :
    Set.Finite {a : 𝓞 K |
      ‖numberEmbedding K (a : K)‖ ≤ R} := by
  let L := NumberField.mixedEmbedding.euclidean.integerLattice K
  let _ : DiscreteTopology L := by
    dsimp [L]
    infer_instance
  have hLclosed : IsClosed (X := K_ℝ[K]) L :=
    @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
  have hfinite :
      Set.Finite (Metric.closedBall (0 : K_ℝ[K]) R ∩ (L : Set K_ℝ[K])) :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall hLclosed
  let e : (𝓞 K) ↪ K_ℝ[K] :=
    ⟨fun a => numberEmbedding K (a : K),
      (numberEmbedding_injective K).comp
        NumberField.RingOfIntegers.coe_injective⟩
  refine (hfinite.preimage e.injective.injOn).subset ?_
  intro a ha
  change e a ∈ Metric.closedBall (0 : K_ℝ[K]) R ∩ (L : Set K_ℝ[K])
  constructor
  · simpa [e, Metric.mem_closedBall, dist_zero_left] using ha
  · change (NumberField.mixedEmbedding.euclidean.toMixed K) (e a) ∈
      NumberField.mixedEmbedding.integerLattice K
    exact ⟨a, by simp [e, numberEmbedding]⟩

theorem finite_integralMatrices_norm_le {n m : ℕ} (R : ℝ) :
    Set.Finite {A : IntegralMatrix K n m | ‖embedMatrix A‖ ≤ R} := by
  refine (Set.Finite.pi' fun _ : Fin n =>
    Set.Finite.pi' fun _ : Fin m => finite_integralElements_norm_le R).subset ?_
  intro A hA i j
  exact (norm_entry_le_frobenius (embedMatrix A) i j).trans hA

theorem finite_scaledSupport_integralMatrices {n m : ℕ}
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    Set.Finite {A : IntegralMatrix K n m |
      f (T⁻¹ • embedMatrix A) ≠ 0} := by
  obtain ⟨R, hR, hsupport⟩ := h_f.exists_support_radius
  refine (finite_integralMatrices_norm_le (R * T)).subset ?_
  intro A hA
  have hscaled := hsupport _ hA
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hT] at hscaled
  have hTne : T ≠ 0 := hT.ne'
  calc
    ‖embedMatrix A‖ = T * (T⁻¹ * ‖embedMatrix A‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ hTne, one_mul]
    _ ≤ T * R := mul_le_mul_of_nonneg_left hscaled hT.le
    _ = R * T := mul_comm _ _

theorem summable_scaled_integralMatrices {n m : ℕ}
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    Summable (fun A : IntegralMatrix K n m =>
      f (T⁻¹ • embedMatrix A)) := by
  exact summable_of_hasFiniteSupport
    (finite_scaledSupport_integralMatrices f h_f hT)

end IntegralPoints

end Katznelson
