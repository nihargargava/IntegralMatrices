import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Admissible test functions

This file encodes Hypothesis `hy:admissible` in `papers/katznelson.tex` using
the ambient Euclidean structure supplied by Lean.  For number-field spaces,
the author has approved this as a local metric adaptation in the
admissibility/Riemann subsystem: it is not definitionally the
discriminant-scaled trace metric of `eq:norm`.  The exact manuscript Haar
normalization used in the main term is proved separately in
`Counting/MainTermNormalization.lean`.  No norm-equivalence assertion is
silently used to identify exact constants.
-/

namespace Katznelson

open MeasureTheory Set
open scoped MeasureTheory

section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

/- [Lean infrastructure for paper hypothesis `hy:admissible`, lines 532--548]
Borel measurability for the norm topology, independent of any ambient
   `MeasurableSpace` instance selected elsewhere in the development. -/
noncomputable def IsBorelMeasurable (f : X → ℝ) : Prop :=
  let _ : MeasurableSpace X := borel X
  Measurable f

/- [Lean infrastructure for paper hypothesis `hy:admissible`, lines 532--548]
Euclidean Hausdorff volume in the dimension of a real normed space. -/
noncomputable def euclideanIntegral (g : X → ℝ) : ℝ :=
  let _ : MeasurableSpace X := borel X
  let _ : BorelSpace X := ⟨rfl⟩
  ∫ x, g x ∂(μHE[Module.finrank ℝ X] : Measure X)

/- [Lean infrastructure for paper hypothesis `hy:admissible`, lines 532--548]
Integrability for the same canonical Euclidean measure.  Keeping this
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

/- [paper, hypothesis `hy:admissible`, lines 532--548] The paper's
`E_f(x, ε) = sup_{‖x-y‖ ≤ ε} |f(x)-f(y)|`. -/
noncomputable def errorFunction (f : X → ℝ) (x : X) (ε : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ y : X, dist x y ≤ ε ∧ r = |f x - f y|}

/- [paper, hypothesis `hy:admissible`, lines 532--548] An admissible function
is compactly supported, bounded, measurable, and has the uniform
subspace-integral estimate required there.  Integrability is recorded
explicitly because Lean's integral is otherwise defined to be zero for a
nonintegrable function. -/
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

/- [Lean infrastructure for paper `re:help`, lines 550--562] This is the
   analytic assertion obtained after replacing the original range
   `0 < ε ≤ 1` by `0 < ε ≤ εMax`.  Its constant is still uniform in the
   nonzero subspace, exactly as in `hy:admissible`.  The paper's remark says
   this follows after updating the constant; the bridge is kept as a named
   target rather than silently assumed. -/
structure AdmissibleErrorControlUpTo (f : X → ℝ) (εMax : ℝ) : Prop where
  error_integrable :
    ∀ (V : Submodule ℝ X), V ≠ ⊥ → ∀ ε : ℝ, 0 < ε → ε ≤ εMax →
      EuclideanIntegrable (fun x : V => errorFunction f (x : X) ε)
  error_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Submodule ℝ X), V ≠ ⊥ → ∀ ε : ℝ, 0 < ε → ε ≤ εMax →
      euclideanIntegral (fun x : V => errorFunction f (x : X) ε) ≤ C * ε

/- [derived consequence of paper `hy:admissible`, lines 532--549] The
   original admissibility hypothesis is exactly the updated control through
   the manuscript's base threshold `1`. -/
theorem Admissible.errorControlUpTo_one {f : X → ℝ} (h_f : Admissible f) :
    AdmissibleErrorControlUpTo f 1 := by
  exact ⟨h_f.error_integrable, h_f.error_bound⟩

/- [Lean infrastructure] Restricting an already established error-control
   range is elementary bookkeeping.  Keeping this monotonicity explicit lets
   later Riemann arguments use the exact threshold supplied by the manuscript
   without silently changing the quantifier range. -/
theorem AdmissibleErrorControlUpTo.mono {f : X → ℝ} {εMax εMax' : ℝ}
    (h : AdmissibleErrorControlUpTo f εMax') (hε : εMax ≤ εMax') :
    AdmissibleErrorControlUpTo f εMax := by
  refine ⟨?_, ?_⟩
  · intro V hV ε hεpos hεle
    exact h.error_integrable V hV ε hεpos (hεle.trans hε)
  · obtain ⟨C, hC, hbound⟩ := h.error_bound
    refine ⟨C, hC, ?_⟩
    intro V hV ε hεpos hεle
    exact hbound V hV ε hεpos (hεle.trans hε)

/- [derived consequence of hypothesis `hy:admissible`,
   `papers/katznelson.tex`, lines 541--548] The defining error estimate
   already proves every smaller positive cutoff.  The separate extension to
   a cutoff greater than one is the content of the manuscript's remark
   `re:help`, not an implicit consequence used here. -/
theorem Admissible.errorControlUpTo_of_le_one {f : X → ℝ} (h_f : Admissible f)
    {εMax : ℝ} (hε : εMax ≤ 1) :
    AdmissibleErrorControlUpTo f εMax := by
  exact h_f.errorControlUpTo_one.mono hε

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
