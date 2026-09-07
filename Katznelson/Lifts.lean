import Katznelson.Foundations
import Katznelson.Lattice
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Lifts of algebraic codes

This file formalizes the objects introduced in Section `se:lifts_of_codes` of
`papers/katznelson.tex` (arXiv:2510.11673).  The TeX source is authoritative;
the averaging and convergence estimates are developed after these definitions.
-/

namespace Katznelson

open Set
open scoped BigOperators NumberField

section

variable {K : Type*} [Field K] [NumberField K]

/- The paper's `k_𝓟 = 𝓞 K / 𝓟`. -/
abbrev residueField (P : PrimeIdeal K) := 𝓞 K ⧸ P.1

/- A nonzero prime ideal of the ring of integers is maximal, so its quotient
   is a finite field.  The instance is local to the quotient type because
   Mathlib keeps quotient fields as non-global definitions. -/
noncomputable instance residueField.field (P : PrimeIdeal K) :
    Field (residueField P) := by
  exact Ideal.Quotient.field P.1

noncomputable instance residueField.finite (P : PrimeIdeal K) :
    Finite (residueField P) := by
  infer_instance

noncomputable instance residueField.fintype (P : PrimeIdeal K) :
    Fintype (residueField P) := Fintype.ofFinite _

/- Reduction modulo `𝓟`, coordinatewise on `𝓞 K^n`. -/
def reduce (P : PrimeIdeal K) {n : ℕ} :
    (Fin n → 𝓞 K) → (Fin n → residueField P) :=
  fun x i => Ideal.Quotient.mk P.1 (x i)

@[simp] theorem reduce_apply (P : PrimeIdeal K) {n : ℕ}
    (x : Fin n → 𝓞 K) (i : Fin n) :
    reduce P x i = Ideal.Quotient.mk P.1 (x i) := rfl

/- The Grassmannian of `s`-dimensional `k_𝓟`-subspaces of `k_𝓟^n`. -/
abbrev Code (P : PrimeIdeal K) (n s : ℕ) :=
  {S : Submodule (residueField P) (Fin n → residueField P) //
    Module.finrank (residueField P) S = s}

/- There are finitely many codes because `k_𝓟^n` is a finite vector space.
   This is the finiteness needed to interpret the paper's uniform average over
   `𝓛(𝓟,s)` once the averaging functional is introduced. -/
noncomputable instance code.finite (P : PrimeIdeal K) (n s : ℕ) :
    Finite (Code P n s) := by
  infer_instance

noncomputable instance code.fintype (P : PrimeIdeal K) (n s : ℕ) :
    Fintype (Code P n s) := Fintype.ofFinite _

/- The full preimage of a code under reduction.  This is the unscaled lift
   `Λ ⊆ 𝓞 K^n` in equation (eq:def_of_L) of the paper. -/
def rawLift (P : PrimeIdeal K) {n s : ℕ} (S : Code P n s) :
    Submodule (𝓞 K) (Fin n → 𝓞 K) where
  carrier := (reduce P) ⁻¹' S.1
  zero_mem' := by
    change reduce P 0 ∈ S.1
    rw [show reduce P 0 = 0 by
      ext i
      simp [reduce]]
    exact S.1.zero_mem
  add_mem' := by
    intro x y hx hy
    change reduce P (x + y) ∈ S.1
    rw [show reduce P (x + y) = reduce P x + reduce P y by
      ext i
      simp [reduce]]
    exact S.1.add_mem hx hy
  smul_mem' := by
    intro a x hx
    change reduce P (a • x) ∈ S.1
    rw [show reduce P (a • x) = (Ideal.Quotient.mk P.1 a) • reduce P x by
      ext i
      simp [reduce, Pi.smul_apply]]
    exact S.1.smul_mem (Ideal.Quotient.mk P.1 a) hx

theorem mem_rawLift_iff (P : PrimeIdeal K) {n s : ℕ} (S : Code P n s)
    (x : Fin n → 𝓞 K) :
    x ∈ rawLift P S ↔ reduce P x ∈ S.1 := Iff.rfl

/- The coordinatewise copy of `𝓟` inside `𝓞 K^n`, corresponding to
   `(𝓟 𝓞_K)^n ⊆ Λ` in equation (eq:def_of_L). -/
def primePowerVectors (P : PrimeIdeal K) (n : ℕ) :
    Submodule (𝓞 K) (Fin n → 𝓞 K) where
  carrier := {x | ∀ i, x i ∈ P.1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i
    exact P.1.add_mem (hx i) (hy i)
  smul_mem' := by
    intro a x hx i
    exact P.1.smul_mem a (hx i)

theorem primePowerVectors_le_rawLift (P : PrimeIdeal K)
    {n s : ℕ} (S : Code P n s) :
    primePowerVectors P n ≤ rawLift P S := by
  intro x hx
  change reduce P x ∈ S.1
  rw [show reduce P x = 0 by
    ext i
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hx i)]
  exact S.1.zero_mem

/- Coordinatewise canonical embedding into `K_ℝ`. -/
noncomputable def embedVector (x : Fin n → 𝓞 K) : Fin n → K_ℝ[K] :=
  fun i => numberEmbedding K (x i)

/- Equation (eq:def_of_L): `T_𝓟 = N(𝓟)^((1-s/n)/d)`.  We use `Real.rpow`
   because the exponent is generally real. -/
noncomputable def liftScale (P : PrimeIdeal K) (n s : ℕ) : ℝ :=
  Real.rpow (idealNorm P : ℝ)
    ((1 - (s : ℝ) / (n : ℝ)) / (degree K : ℝ))

theorem liftScale_pos (P : PrimeIdeal K) (n s : ℕ) :
    0 < liftScale P n s := by
  rw [liftScale]
  apply Real.rpow_pos_of_pos
  have hnorm : idealNorm P ≠ 0 := by
    intro hzero
    apply P.2.2
    exact Ideal.absNorm_eq_zero_iff.mp hzero
  exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hnorm)

/- The scale in equation (eq:def_of_L) has exactly the normalization used in
   the fixed-rank term: for `s ≤ n`, its `k n d`-th power is the algebraic
   norm power `N(P)^(k(n-s))`. -/
theorem liftScale_pow_eq_idealNorm_pow (P : PrimeIdeal K)
    {n s k : ℕ} (hsn : s ≤ n) (hn : 0 < n) :
    (liftScale P n s) ^ (k * n * degree K) =
      (idealNorm P : ℝ) ^ (k * (n - s)) := by
  have hnorm : idealNorm P ≠ 0 := by
    intro hzero
    apply P.2.2
    exact Ideal.absNorm_eq_zero_iff.mp hzero
  have hq : 0 < (idealNorm P : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hnorm)
  have hd : 0 < (degree K : ℝ) := by
    exact_mod_cast (show 0 < degree K from Module.finrank_pos)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hexp :
      ((1 - (s : ℝ) / (n : ℝ)) / (degree K : ℝ)) *
          ((k * n * degree K : ℕ) : ℝ) =
        ((k * (n - s) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hsn]
    field_simp [ne_of_gt hn', ne_of_gt hd]
  calc
    (liftScale P n s) ^ (k * n * degree K) =
        (liftScale P n s) ^ ((k * n * degree K : ℕ) : ℝ) := by
      symm
      exact Real.rpow_natCast _ _
    _ = (idealNorm P : ℝ) ^
          (((1 - (s : ℝ) / (n : ℝ)) / (degree K : ℝ)) *
            ((k * n * degree K : ℕ) : ℝ)) := by
      rw [liftScale, Real.rpow_mul hq.le]
      rfl
    _ = (idealNorm P : ℝ) ^ ((k * (n - s) : ℕ) : ℝ) := by
      rw [hexp]
    _ = (idealNorm P : ℝ) ^ (k * (n - s)) := by
      exact Real.rpow_natCast _ _

/- The normalized lattice `T_𝓟⁻¹ Λ` associated to a code. -/
noncomputable def normalizedLift (P : PrimeIdeal K) {n s : ℕ} (S : Code P n s) :
    Set (Fin n → K_ℝ[K]) :=
  (fun x => (liftScale P n s)⁻¹ • embedVector x) '' (rawLift P S : Set (Fin n → 𝓞 K))

theorem mem_normalizedLift_iff (P : PrimeIdeal K) {n s : ℕ} (S : Code P n s)
    (x : Fin n → K_ℝ[K]) :
    x ∈ normalizedLift P S ↔
      ∃ y ∈ rawLift P S, x = (liftScale P n s)⁻¹ • embedVector y := by
  change (∃ y ∈ rawLift P S,
    (liftScale P n s)⁻¹ • embedVector y = x) ↔ _
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, hxy.symm⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, hxy.symm⟩

/- We index the finite collection of lifts by its code.  This keeps the
   construction faithful to the paper while avoiding a quotient by equality
   of sets; `normalizedLift` is the map to the actual lattice in `K_ℝ^n`. -/
abbrev Lifts (K : Type*) [Field K] [NumberField K]
    (P : PrimeIdeal K) (n s : ℕ) := Code P n s

notation "𝓛[" K "," P "," n "," s "]" => Lifts K P n s

theorem code_rank (P : PrimeIdeal K) {n s : ℕ} (S : 𝓛[K, P, n, s]) :
    Module.finrank (residueField P) S.1 = s := S.2

/- Matrices in `Λ^m`, represented by integral matrices whose columns lie in
   the raw lift.  This is the matrix form of the inner sum in (eq:nthmoment). -/
def matricesInLift (P : PrimeIdeal K) {n m s : ℕ} (S : Code P n s) :
    Set (IntegralMatrix K n m) :=
  {A | ∀ j, (fun i => A i j) ∈ rawLift P S}

theorem mem_matricesInLift_iff (P : PrimeIdeal K) {n m s : ℕ}
    (S : Code P n s) (A : IntegralMatrix K n m) :
    A ∈ matricesInLift P S ↔
      ∀ j, (fun i => A i j) ∈ rawLift P S := Iff.rfl

/- The lattice sum attached to one code, with the normalization from
   `normalizedLift`. -/
noncomputable def liftCodeSum (P : PrimeIdeal K) {n m s : ℕ}
    (S : Code P n s) (f : M n m (K_ℝ[K]) → ℝ) : ℝ :=
  ∑' A : {A : IntegralMatrix K n m // A ∈ matricesInLift P S},
    f ((liftScale P n s)⁻¹ • embedMatrix A.1)

/- The finite average over `𝓛(𝓟,s)`, now represented by its code index. -/
noncomputable def liftsMoment (P : PrimeIdeal K) (n m s : ℕ)
    (f : M n m (K_ℝ[K]) → ℝ) : ℝ :=
  (Fintype.card (Code P n s) : ℝ)⁻¹ *
    ∑ S : Code P n s, liftCodeSum P S f

end
end Katznelson
