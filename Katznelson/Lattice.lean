import Katznelson.Foundations
import Mathlib.Topology.DiscreteSubset

/-!
# Lattices

The paper defines a lattice as a discrete `ℤ`-submodule of a Euclidean space.
This file records that definition in a form compatible with Mathlib's additive
subgroups, and identifies the standard algebraic-integer lattice supplied by
the canonical embedding.
-/

namespace Katznelson

open Set
open scoped NumberField

section

variable (V : Type*) [AddCommGroup V] [TopologicalSpace V]

structure Lattice where
  carrier : Submodule ℤ V
  discrete' : IsDiscrete (carrier : Set V)

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

end NumberField
end Katznelson
