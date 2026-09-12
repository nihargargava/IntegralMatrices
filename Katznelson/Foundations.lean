import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# Foundations for Integral Matrices of Fixed Rank

The source of the notation and conventions is `papers/katznelson.tex`, the
preprint referenced as arXiv:2510.11673.  The checked-in TeX source remains
the source of truth for this formalization.
-/

namespace Katznelson

open scoped BigOperators Classical NumberField

/- The paper's `M_{n × m}(R)`. -/
abbrev M (n m : ℕ) (R : Type*) := Matrix (Fin n) (Fin m) R

/- [Lean infrastructure; author-approved local metric adaptation] The paper
   writes `K_ℝ = K ⊗_ℚ ℝ`.  We use Mathlib's Euclidean mixed space, rather
   than its supremum-normed mixed space, so finite products carry an `l²`
   geometry.  Its complex-place weights and discriminant scaling are not
   definitionally equation `eq:norm`; the exact manuscript metric and Haar
   normalization are exposed in `Counting/PaperMetric.lean` and
   `Counting/MainTermNormalization.lean`.  The raw norm is used only for the
   author-approved admissibility/Riemann implementation and coarse bounds. -/
abbrev KReal (K : Type*) [Field K] [NumberField K] :=
  NumberField.mixedEmbedding.euclidean.mixedSpace K
notation "K_ℝ[" K "]" => KReal K

/- Freeze the inherited Euclidean instances before introducing the
specialized matrix instances below, avoiding recursive instance search. -/
@[instance_reducible] noncomputable def kRealNormedAddCommGroup
    (K : Type*) [Field K] [NumberField K] : NormedAddCommGroup K_ℝ[K] :=
  inferInstance

@[instance_reducible] noncomputable def kRealNormedSpace
    (K : Type*) [Field K] [NumberField K] : NormedSpace ℝ K_ℝ[K] :=
  inferInstance

@[instance_reducible] noncomputable def kRealNormSMulClass
    (K : Type*) [Field K] [NumberField K] : NormSMulClass ℝ K_ℝ[K] :=
  inferInstance

/- [Lean infrastructure; author-approved local metric adaptation] Fix the
raw Euclidean `l²` matrix norm globally for matrices over `K_ℝ`.
Mathlib leaves matrix norms scoped because several choices are useful; a
specialized instance here prevents the supremum and Frobenius topologies
from being selected inconsistently in downstream lattice subtypes. -/
noncomputable instance kRealMatrixNormedAddCommGroup
    {K : Type*} [Field K] [NumberField K] {n m : ℕ} :
    NormedAddCommGroup (M n m (K_ℝ[K])) :=
  letI : NormedAddCommGroup K_ℝ[K] := kRealNormedAddCommGroup K
  Matrix.frobeniusNormedAddCommGroup

noncomputable instance kRealMatrixNormedSpace
    {K : Type*} [Field K] [NumberField K] {n m : ℕ} :
    NormedSpace ℝ (M n m (K_ℝ[K])) :=
  @Matrix.frobeniusNormedSpace ℝ (Fin n) (Fin m) K_ℝ[K]
    inferInstance inferInstance Real.normedField
    (kRealNormedAddCommGroup K).toSeminormedAddCommGroup
    (kRealNormedSpace K)

noncomputable instance kRealMatrixNormSMulClass
    {K : Type*} [Field K] [NumberField K] {n m : ℕ} :
    NormSMulClass ℝ (M n m (K_ℝ[K])) :=
  @Matrix.frobeniusNormSMulClass ℝ (Fin n) (Fin m) K_ℝ[K]
    inferInstance inferInstance inferInstance
    (kRealNormedAddCommGroup K).toSeminormedAddCommGroup
    inferInstance (kRealNormSMulClass K)

noncomputable instance kRealMatrixMeasurableSpace
    {K : Type*} [Field K] [NumberField K] {n m : ℕ} :
    MeasurableSpace (M n m (K_ℝ[K])) := borel (M n m (K_ℝ[K]))

instance kRealMatrixBorelSpace
    {K : Type*} [Field K] [NumberField K] {n m : ℕ} :
    BorelSpace (M n m (K_ℝ[K])) := ⟨rfl⟩

/- The mixed embedding, transported into the Euclidean realization. -/
noncomputable def numberEmbedding
    (K : Type*) [Field K] [NumberField K] (x : K) : K_ℝ[K] :=
  (NumberField.mixedEmbedding.euclidean.toMixed K).symm
    (NumberField.mixedEmbedding K x)

@[simp]
theorem numberEmbedding_zero
    (K : Type*) [Field K] [NumberField K] :
    numberEmbedding K 0 = 0 := by
  simp [numberEmbedding]

@[simp]
theorem numberEmbedding_add
    (K : Type*) [Field K] [NumberField K] (x y : K) :
    numberEmbedding K (x + y) = numberEmbedding K x + numberEmbedding K y := by
  simp [numberEmbedding]

@[simp]
theorem numberEmbedding_zsmul
    (K : Type*) [Field K] [NumberField K] (z : ℤ) (x : K) :
    numberEmbedding K (z • x) = z • numberEmbedding K x := by
  unfold numberEmbedding
  rw [map_zsmul, map_zsmul]

@[simp]
theorem numberEmbedding_rat_smul
    (K : Type*) [Field K] [NumberField K] (q : ℚ) (x : K) :
    numberEmbedding K (q • x) = (q : ℝ) • numberEmbedding K x := by
  apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
  change NumberField.mixedEmbedding K (q • x) =
    (q : ℝ) • NumberField.mixedEmbedding K x
  ext w <;> simp [Algebra.smul_def]

theorem numberEmbedding_injective
    (K : Type*) [Field K] [NumberField K] :
    Function.Injective (numberEmbedding K) :=
  (NumberField.mixedEmbedding.euclidean.toMixed K).symm.injective.comp
    (NumberField.mixedEmbedding_injective K)

/- Mathlib's Euclidean realization has the correct ring structure, but its
   `toMixed` map is only packaged as a continuous linear equivalence.  The
   following elementary coordinate calculation records that this realization
   still transports the pointwise multiplication from the ordinary mixed
   space.  It is what lets the paper's `K_ℝ`-scalar action be represented by
   multiplication by the embedded element. -/
private theorem euclidean_toMixed_one
    (K : Type*) [Field K] [NumberField K] :
    NumberField.mixedEmbedding.euclidean.toMixed K (1 : K_ℝ[K]) = 1 := by
  ext <;> rfl

theorem euclidean_toMixed_mul
    (K : Type*) [Field K] [NumberField K] (x y : K_ℝ[K]) :
    NumberField.mixedEmbedding.euclidean.toMixed K (x * y) =
      NumberField.mixedEmbedding.euclidean.toMixed K x *
        NumberField.mixedEmbedding.euclidean.toMixed K y := by
  ext <;> rfl

private theorem euclidean_mul_comm
    (K : Type*) [Field K] [NumberField K] (x y : K_ℝ[K]) :
    x * y = y * x := by
  apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
  rw [euclidean_toMixed_mul K x y, euclidean_toMixed_mul K y x]
  ext <;> simp [mul_comm]

/- The paper's scalar action of `K` on `K_ℝ = K ⊗_ℚ ℝ`, realized without an
   additional axiom: `c • x` is multiplication by the Euclidean mixed-space
   image of `c`. -/
noncomputable def numberEmbeddingRingHom
    (K : Type*) [Field K] [NumberField K] : K →+* K_ℝ[K] where
  toFun := numberEmbedding K
  map_zero' := numberEmbedding_zero K
  map_add' := numberEmbedding_add K
  map_one' := by
    apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
    simp only [numberEmbedding, ContinuousLinearEquiv.apply_symm_apply, map_one]
    exact euclidean_toMixed_one K
  map_mul' := by
    intro x y
    apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
    change NumberField.mixedEmbedding K (x * y) = _
    rw [map_mul]
    exact (euclidean_toMixed_mul K (numberEmbedding K x) (numberEmbedding K y)).symm

noncomputable instance kRealAlgebra
    (K : Type*) [Field K] [NumberField K] : Algebra K K_ℝ[K] :=
  (numberEmbeddingRingHom K).toAlgebra' (by
    intro x y
    exact euclidean_mul_comm K ((numberEmbeddingRingHom K) x) y)

@[simp]
theorem numberEmbeddingRingHom_apply
    (K : Type*) [Field K] [NumberField K] (x : K) :
    numberEmbeddingRingHom K x = numberEmbedding K x := rfl

theorem kReal_smul_eq_mul
    (K : Type*) [Field K] [NumberField K] (c : K) (x : K_ℝ[K]) :
    c • x = numberEmbedding K c * x := by
  rw [Algebra.smul_def]
  rfl

/- The `K`-action on the mixed space commutes with the real scalar action.
   This elementary compatibility is needed to regard the real span of an
   integral row module as a `K`-module when the successive minima are taken
   in that span. -/
theorem kReal_smul_comm_real
    (K : Type*) [Field K] [NumberField K] (c : K) (r : ℝ) (x : K_ℝ[K]) :
    c • (r • x) = r • (c • x) := by
  apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
  rw [kReal_smul_eq_mul K c (r • x), kReal_smul_eq_mul K c x]
  rw [euclidean_toMixed_mul,
    (NumberField.mixedEmbedding.euclidean.toMixed K).map_smul,
    (NumberField.mixedEmbedding.euclidean.toMixed K).map_smul]
  rw [euclidean_toMixed_mul]
  ext w <;> simp [smul_eq_mul, mul_comm]

noncomputable instance kRealSMulCommClass
    (K : Type*) [Field K] [NumberField K] :
    SMulCommClass K ℝ K_ℝ[K] where
  smul_comm := kReal_smul_comm_real K

/- The same two scalar compatibilities for arbitrary `K_ℝ` scalars.  The
   mixed-space ring is coordinatewise, so these are elementary consequences
   of the real scalar action and are used to transport the action to row-span
   subtypes. -/
theorem kReal_smul_comm_real_all
    (K : Type*) [Field K] [NumberField K] (c x : K_ℝ[K]) (r : ℝ) :
    c • (r • x) = r • (c • x) := by
  apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
  calc
    (NumberField.mixedEmbedding.euclidean.toMixed K) (c • (r • x)) =
        (NumberField.mixedEmbedding.euclidean.toMixed K) (c * (r • x)) := by
          rw [smul_eq_mul]
    _ = (NumberField.mixedEmbedding.euclidean.toMixed K) c *
        (NumberField.mixedEmbedding.euclidean.toMixed K) (r • x) :=
      euclidean_toMixed_mul K c (r • x)
    _ = (NumberField.mixedEmbedding.euclidean.toMixed K) c *
        (r • (NumberField.mixedEmbedding.euclidean.toMixed K) x) := by
          rw [(NumberField.mixedEmbedding.euclidean.toMixed K).map_smul]
    _ = r • ((NumberField.mixedEmbedding.euclidean.toMixed K) c *
        (NumberField.mixedEmbedding.euclidean.toMixed K) x) := by
          ext w <;> simp [smul_eq_mul]
    _ = r • (NumberField.mixedEmbedding.euclidean.toMixed K) (c * x) := by
          rw [euclidean_toMixed_mul]
    _ = r • (NumberField.mixedEmbedding.euclidean.toMixed K) (c • x) := by
          rw [smul_eq_mul]

theorem kReal_smul_assoc_real
    (K : Type*) [Field K] [NumberField K] (r : ℝ) (c x : K_ℝ[K]) :
    (r • c) • x = r • (c • x) := by
  apply (NumberField.mixedEmbedding.euclidean.toMixed K).injective
  calc
    (NumberField.mixedEmbedding.euclidean.toMixed K) ((r • c) • x) =
        (NumberField.mixedEmbedding.euclidean.toMixed K) ((r • c) * x) := by
          rw [smul_eq_mul]
    _ = (NumberField.mixedEmbedding.euclidean.toMixed K) (r • c) *
        (NumberField.mixedEmbedding.euclidean.toMixed K) x :=
      euclidean_toMixed_mul K (r • c) x
    _ = (r • (NumberField.mixedEmbedding.euclidean.toMixed K) c) *
        (NumberField.mixedEmbedding.euclidean.toMixed K) x := by
          rw [(NumberField.mixedEmbedding.euclidean.toMixed K).map_smul]
    _ = r • ((NumberField.mixedEmbedding.euclidean.toMixed K) c *
        (NumberField.mixedEmbedding.euclidean.toMixed K) x) := by
          ext w <;> simp [smul_eq_mul]
    _ = r • (NumberField.mixedEmbedding.euclidean.toMixed K) (c * x) := by
          rw [euclidean_toMixed_mul]
    _ = r • (NumberField.mixedEmbedding.euclidean.toMixed K) (c • x) := by
          rw [smul_eq_mul]

abbrev IntegralMatrix (K : Type*) [Field K] [NumberField K] (n m : ℕ) :=
  M n m (𝓞 K)

noncomputable def degree (K : Type*) [Field K] [NumberField K] : ℕ :=
  Module.finrank ℚ K

noncomputable def matrixRank {n m : ℕ} {R : Type*} [CommSemiring R]
    (A : M n m R) : ℕ := A.rank

/- An integral matrix viewed over its fraction field.  Algebraic rank in the
   paper is always taken over `K`, not over the product algebra `K_ℝ`. -/
def algebraicMatrix
    {K : Type*} [Field K] [NumberField K] {n m : ℕ}
    (A : IntegralMatrix K n m) : M n m K :=
  fun i j => (A i j : K)

noncomputable def integralMatrixRank
    {K : Type*} [Field K] [NumberField K] {n m : ℕ}
    (A : IntegralMatrix K n m) : ℕ :=
  matrixRank (algebraicMatrix A)

noncomputable def embedMatrix
    {K : Type*} [Field K] [NumberField K] {n m : ℕ}
    (A : IntegralMatrix K n m) : M n m (K_ℝ[K]) :=
  fun i j => numberEmbedding K (A i j)

/- Prime ideals and their ideal norms, as in the paper's `𝓟` and `𝓝(𝓟)`. -/
/- The paper's prime ideals are the nonzero prime ideals of `𝓞 K`.  The
   nonzero condition is important here: it makes the residue quotient a
   finite field, as used in the lifts-of-codes section. -/
abbrev PrimeIdeal (K : Type*) [Field K] [NumberField K] :=
  {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥}

noncomputable instance primeIdeal.isMaximal
    {K : Type*} [Field K] [NumberField K] (P : PrimeIdeal K) : P.1.IsMaximal := by
  exact P.2.1.isMaximal P.2.2

noncomputable def idealNorm {K : Type*} [Field K] [NumberField K]
    (P : PrimeIdeal K) : ℕ := Ideal.absNorm P.1

notation "𝓝(" P ")" => idealNorm P

/- The paper's `𝓛(𝓟,s)`; its lattice structure is introduced in the
   lifts-of-codes module after the lattice foundations are proved. -/
end Katznelson
