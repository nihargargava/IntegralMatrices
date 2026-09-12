import Katznelson.Foundations
import Katznelson.Counting.PaperMetric
import Mathlib.Topology.DiscreteSubset
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Lattices

The paper defines a lattice as a discrete `ℤ`-submodule of a Euclidean space.
This file records that definition in a form compatible with Mathlib's additive
subgroups, and identifies the standard algebraic-integer lattice supplied by
the canonical embedding.
-/

namespace Katznelson

open Set Module
open scoped NumberField

section

variable (V : Type*) [AddCommGroup V] [TopologicalSpace V]

structure Lattice where
  carrier : Submodule ℤ V
  discrete' : IsDiscrete (carrier : Set V)

/- [Lean infrastructure] This is the covering clause appearing in the
   manuscript's definition of `ρ` (lines 433--437).  The separate numerical
   covering radius is introduced only after the nearest-point and Voronoi
   lemmas are proved. -/
def LatticeCovering {E : Type*} [NormedAddCommGroup E]
    (L : Submodule ℤ E) (R : ℝ) : Prop :=
  ∀ x : E, ∃ v : L, dist x (v : E) ≤ R

instance : SetLike (Lattice V) V where
  coe L := L.carrier
  coe_injective := by
    intro L₁ L₂ h
    cases L₁ with
    | mk c₁ hd₁ =>
      cases L₂ with
      | mk c₂ hd₂ =>
        simp only at h
        congr
        exact SetLike.coe_injective h

@[simp] theorem mem_carrier {L : Lattice V} {x : V} :
    x ∈ L.carrier ↔ x ∈ (L : Set V) := Iff.rfl

end

section DiscreteCriterion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable local instance rationalModule : Module ℚ E :=
  Module.compHom E (algebraMap ℚ ℝ)

/- [Lean infrastructure] A finitely generated integral module whose rational
   and real spans have the same dimension is discrete.  This is a general
   encoding lemma used below for the rational orthogonal projection in the
   paper's low-rank induction (papers/katznelson.tex, lines 1475--1479).
   It is not an alternative proof of a paper estimate: the application still
   has to prove the rational-span dimension equality from the manuscript's
   number-field embedding. -/
theorem discreteTopology_of_finrank_eq
    (L : Submodule ℤ E) [Module.Finite ℤ L]
    (h : Set.finrank ℚ (L : Set E) = Set.finrank ℝ (L : Set E)) :
    DiscreteTopology L := by
  letI : IsAddTorsionFree E := IsAddTorsionFree.of_module_rat E
  letI : IsTorsionFree ℤ E := by infer_instance
  letI : IsTorsionFree ℤ L := by infer_instance
  letI : Module.Free ℤ L := by infer_instance
  let I := Module.Free.ChooseBasisIndex ℤ L
  letI : Fintype I := Fintype.ofFinite I
  let b : Basis I ℤ L := Module.Free.chooseBasis ℤ L
  let bE : I → E := fun i => b i
  have hLIz : LinearIndependent ℤ bE := by
    exact b.linearIndependent.map' L.subtype
      (LinearMap.ker_eq_bot.mpr L.injective_subtype)
  have hLIq : LinearIndependent ℚ bE := by
    exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp hLIz
  have hspanQ : Submodule.span ℚ (Set.range bE) =
      Submodule.span ℚ (L : Set E) := by
    apply le_antisymm
    · exact Submodule.span_mono (by
        rintro _ ⟨i, rfl⟩
        exact (b i).property)
    · rw [Submodule.span_le]
      intro x hx
      let xL : L := ⟨x, hx⟩
      change (xL : E) ∈ Submodule.span ℚ (Set.range bE)
      have heq : (xL : E) = ∑ i,
          ((b.repr xL) i : ℚ) • bE i := by
        rw [← congrArg (fun z : L => (z : E)) (b.sum_repr xL)]
        change L.subtype (∑ i, (b.repr xL) i • b i) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp [bE, Int.cast_smul_eq_zsmul ℚ]
      rw [heq]
      apply Submodule.sum_mem
      intro i hi
      have hi' := Submodule.smul_mem
        (Submodule.span ℚ (Set.range bE))
        ((b.repr ⟨x, hx⟩) i : ℚ)
        (Submodule.subset_span (Set.mem_range_self i))
      simpa [bE, Int.cast_smul_eq_zsmul ℚ] using hi'
  have hspanR : Submodule.span ℝ (Set.range bE) =
      Submodule.span ℝ (L : Set E) := by
    apply le_antisymm
    · exact Submodule.span_mono (by
        rintro _ ⟨i, rfl⟩
        exact (b i).property)
    · rw [Submodule.span_le]
      intro x hx
      let xL : L := ⟨x, hx⟩
      change (xL : E) ∈ Submodule.span ℝ (Set.range bE)
      have heq : (xL : E) = ∑ i,
          ((b.repr xL) i : ℝ) • bE i := by
        rw [← congrArg (fun z : L => (z : E)) (b.sum_repr xL)]
        change L.subtype (∑ i, (b.repr xL) i • b i) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp [bE, Int.cast_smul_eq_zsmul ℝ]
      rw [heq]
      apply Submodule.sum_mem
      intro i hi
      have hi' := Submodule.smul_mem
        (Submodule.span ℝ (Set.range bE))
        ((b.repr ⟨x, hx⟩) i : ℝ)
        (Submodule.subset_span (Set.mem_range_self i))
      simpa [bE, Int.cast_smul_eq_zsmul ℝ] using hi'
  have hQcard : Module.finrank ℚ
      (Submodule.span ℚ (L : Set E)) = Fintype.card I := by
    rw [← hspanQ]
    exact finrank_span_eq_card hLIq
  have hRcard : Module.finrank ℝ
      (Submodule.span ℝ (Set.range bE)) = Fintype.card I := by
    calc
      Module.finrank ℝ (Submodule.span ℝ (Set.range bE)) =
          Module.finrank ℝ (Submodule.span ℝ (L : Set E)) := by
            rw [hspanR]
      _ = Module.finrank ℚ (Submodule.span ℚ (L : Set E)) := by
        simpa [Set.finrank] using h.symm
      _ = Fintype.card I := hQcard
  have hLIr : LinearIndependent ℝ bE := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    simpa [Set.finrank] using hRcard.symm
  let F : Submodule ℝ E := Submodule.span ℝ (Set.range bE)
  let bF : I → F := fun i => ⟨bE i, Submodule.subset_span (Set.mem_range_self i)⟩
  have hLIF : LinearIndependent ℝ bF := by
    apply LinearIndependent.of_comp F.subtype
    simpa [Function.comp_def, bF] using hLIr
  have himage : F.subtype '' Set.range bF = Set.range bE := by
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨bF i, ⟨i, rfl⟩, by rfl⟩
  have hspanF : Submodule.span ℝ (Set.range bF) = ⊤ := by
    apply (Submodule.map_injective_of_injective
      (Submodule.injective_subtype F))
    rw [Submodule.map_span, himage]
    rw [Submodule.map_subtype_top]
  let bR : Basis I ℝ F := Basis.mk hLIF (eq_top_iff.mp hspanF)
  let target : Submodule ℤ F := Submodule.span ℤ (Set.range bR)
  let f : L → target := fun x => by
    have hxF : (x : E) ∈ F := by
      change (x : E) ∈ Submodule.span ℝ (Set.range bE)
      rw [hspanR]
      exact Submodule.subset_span (SetLike.coe_mem x)
    let xF : F := ⟨(x : E), hxF⟩
    refine ⟨xF, ?_⟩
    · have hsum : (∑ i, (b.repr x) i • bF i) = xF := by
        apply Subtype.ext
        change F.subtype (∑ i, (b.repr x) i • bF i) = (xF : E)
        rw [map_sum]
        change (∑ i, (b.repr x) i • bE i) = (x : E)
        have h := congrArg (fun z : L => (z : E)) (b.sum_repr x)
        change L.subtype (∑ i, (b.repr x) i • b i) = (x : E) at h
        rw [map_sum] at h
        simpa [bE] using h
      have hrepr : (∑ i, (b.repr x) i • bR i) = xF := by
        simpa [bR] using hsum
      rw [← hrepr]
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.smul_mem target (b.repr x i)
        (Submodule.subset_span (Set.mem_range_self i))
  letI : DiscreteTopology target := by
    dsimp [target]
    infer_instance
  have hcontF : Continuous (fun x : L =>
      (⟨(x : E), by
        change (x : E) ∈ Submodule.span ℝ (Set.range bE)
        rw [hspanR]
        exact Submodule.subset_span (SetLike.coe_mem x)⟩ : F)) := by
    apply Continuous.subtype_mk continuous_subtype_val
  have hcont : Continuous f := by
    apply Continuous.subtype_mk hcontF
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : target => (z : F)) hxy |>
      congrArg (fun z : F => (z : E))
  apply DiscreteTopology.of_continuous_injective hcont hinj

end DiscreteCriterion

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/- Mathlib proves discreteness of the image of `𝓞 K` in the mixed space and
   exposes it as a `Submodule ℤ`.  This is the `𝓞_K ⊂ K_ℝ` lattice in the paper. -/
noncomputable def integralLattice : Lattice K_ℝ[K] where
  carrier := NumberField.mixedEmbedding.euclidean.integerLattice K
  discrete' := by
    rw [SetLike.isDiscrete_iff_discreteTopology]
    infer_instance

@[simp] theorem mem_integralLattice (x : K_ℝ[K]) :
    x ∈ integralLattice (K := K) ↔
      x ∈ NumberField.mixedEmbedding.euclidean.integerLattice K := Iff.rfl

/- derived consequence: the named `integralLattice` has unit covolume for the
manuscript's metric normalization.  This exposes the ambient result from
`PaperMetric.lean` at the paper-facing lattice definition; the exact
coefficient-lattice and pushforward calculations used by the public main
term are proved separately in `Counting/MainTermNormalization.lean`. -/
theorem paperCovolume_integralLattice :
    paperCovolume K (integralLattice (K := K)).carrier = 1 := by
  exact paperCovolume_euclidean_integerLattice K

end NumberField
end Katznelson
