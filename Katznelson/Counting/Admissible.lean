import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Admissible test functions

This file formalizes Hypothesis `hy:admissible` in `papers/katznelson.tex`.
The integration in the hypothesis is with respect to the volume measure on
each real subspace, as in the paper.
-/

namespace Katznelson

open MeasureTheory Set
open scoped MeasureTheory

section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

/- Borel measurability for the norm topology, independent of any ambient
   `MeasurableSpace` instance selected elsewhere in the development. -/
noncomputable def IsBorelMeasurable (f : X → ℝ) : Prop :=
  let _ : MeasurableSpace X := borel X
  Measurable f

/- Euclidean Hausdorff volume in the dimension of a real normed space. -/
noncomputable def euclideanIntegral (g : X → ℝ) : ℝ :=
  let _ : MeasurableSpace X := borel X
  let _ : BorelSpace X := ⟨rfl⟩
  ∫ x, g x ∂(μHE[Module.finrank ℝ X] : Measure X)

/- Integrability for the same canonical Euclidean measure.  Keeping this
   separate prevents the convention `integral = 0` for nonmeasurable
   functions from weakening Hypothesis `hy:admissible`. -/
noncomputable def EuclideanIntegrable (g : X → ℝ) : Prop :=
  let _ : MeasurableSpace X := borel X
  let _ : BorelSpace X := ⟨rfl⟩
  Integrable g (μHE[Module.finrank ℝ X] : Measure X)

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
theorem isBorelMeasurable_iff
    [MeasurableSpace X] [BorelSpace X] (f : X → ℝ) :
    IsBorelMeasurable f ↔ Measurable f := by
  have hmeas : (inferInstance : MeasurableSpace X) = borel X :=
    BorelSpace.measurable_eq
  unfold IsBorelMeasurable
  cases hmeas
  rfl

omit [FiniteDimensional ℝ X] in
theorem euclideanIntegral_eq_integral
    [MeasurableSpace X] [BorelSpace X] (g : X → ℝ) :
    euclideanIntegral g =
      ∫ x, g x ∂(μHE[Module.finrank ℝ X] : Measure X) := by
  have hmeas : (inferInstance : MeasurableSpace X) = borel X :=
    BorelSpace.measurable_eq
  unfold euclideanIntegral
  cases hmeas
  rfl

omit [FiniteDimensional ℝ X] in
theorem euclideanIntegrable_iff
    [MeasurableSpace X] [BorelSpace X] (g : X → ℝ) :
    EuclideanIntegrable g ↔
      Integrable g (μHE[Module.finrank ℝ X] : Measure X) := by
  have hmeas : (inferInstance : MeasurableSpace X) = borel X :=
    BorelSpace.measurable_eq
  unfold EuclideanIntegrable
  cases hmeas
  rfl

/- The paper's `E_f(x, ε) = sup_{‖x-y‖ ≤ ε} |f(x)-f(y)|`. -/
noncomputable def errorFunction (f : X → ℝ) (x : X) (ε : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ y : X, dist x y ≤ ε ∧ r = |f x - f y|}

/-!
An admissible function is compactly supported, bounded, measurable, and has
the uniform subspace-integral estimate required in Hypothesis `hy:admissible`.
-/
structure Admissible (f : X → ℝ) : Prop where
  compactSupport : HasCompactSupport f
  bounded : Bornology.IsBounded (range f)
  measurable : IsBorelMeasurable f
  integrable : EuclideanIntegrable f
  error_integrable :
    ∀ (V : Submodule ℝ X), V ≠ ⊥ → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      EuclideanIntegrable (fun x : V => errorFunction f (x : X) ε)
  error_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Submodule ℝ X), V ≠ ⊥ → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      euclideanIntegral (fun x : V => errorFunction f (x : X) ε) ≤ C * ε

omit [FiniteDimensional ℝ X] in
theorem Admissible.errorFunction_bddAbove {f : X → ℝ}
    (h_f : Admissible f) (x : X) (ε : ℝ) :
    BddAbove {r : ℝ | ∃ y : X, dist x y ≤ ε ∧ r = |f x - f y|} := by
  obtain ⟨C, hC⟩ := h_f.bounded.subset_closedBall (0 : ℝ)
  refine ⟨2 * max C 0, ?_⟩
  rintro r ⟨y, -, rfl⟩
  have hx := hC ⟨x, rfl⟩
  have hy := hC ⟨y, rfl⟩
  rw [Metric.mem_closedBall, Real.dist_0_eq_abs] at hx hy
  calc
    |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
    _ ≤ max C 0 + max C 0 :=
      add_le_add (hx.trans (le_max_left _ _)) (hy.trans (le_max_left _ _))
    _ = 2 * max C 0 := by ring

omit [FiniteDimensional ℝ X] in
theorem Admissible.abs_sub_le_errorFunction {f : X → ℝ}
    (h_f : Admissible f) {x y : X} {ε : ℝ} (hxy : dist x y ≤ ε) :
    |f x - f y| ≤ errorFunction f x ε := by
  apply le_csSup (h_f.errorFunction_bddAbove x ε)
  exact ⟨y, hxy, rfl⟩

omit [FiniteDimensional ℝ X] in
theorem Admissible.errorFunction_nonneg {f : X → ℝ}
    (h_f : Admissible f) {x : X} {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ errorFunction f x ε := by
  have hzero : (0 : ℝ) ∈
      {r : ℝ | ∃ y : X, dist x y ≤ ε ∧ r = |f x - f y|} := by
    exact ⟨x, by simpa using hε, by simp⟩
  exact le_csSup (h_f.errorFunction_bddAbove x ε) hzero

end

end Katznelson
