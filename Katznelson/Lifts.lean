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

/- [paper, Section `se:lifts_of_codes`, lines 1816--1827] The paper's
`k_𝓟 = 𝓞 K / 𝓟`. -/
abbrev residueField (P : PrimeIdeal K) := 𝓞 K ⧸ P.1

/- [Lean infrastructure] A nonzero prime ideal of the ring of integers is
maximal, so its quotient is a finite field.  The following three instances
are local to the quotient type because Mathlib keeps quotient fields as
non-global definitions. -/
noncomputable instance residueField.field (P : PrimeIdeal K) :
    Field (residueField P) := by
  exact Ideal.Quotient.field P.1

noncomputable instance residueField.finite (P : PrimeIdeal K) :
    Finite (residueField P) := by
  infer_instance

noncomputable instance residueField.fintype (P : PrimeIdeal K) :
    Fintype (residueField P) := Fintype.ofFinite _

/- [Lean infrastructure for paper equation `eq:def_of_L`, lines 1816--1827]
Reduction modulo `𝓟`, coordinatewise on `𝓞 K^n`. -/
def reduce (P : PrimeIdeal K) {n : ℕ} :
    (Fin n → 𝓞 K) → (Fin n → residueField P) :=
  fun x i => Ideal.Quotient.mk P.1 (x i)

/- [Lean infrastructure for paper equation `eq:def_of_L`, lines 1816--1827]
Coordinate evaluation of the preceding reduction map. -/
@[simp] theorem reduce_apply (P : PrimeIdeal K) {n : ℕ}
    (x : Fin n → 𝓞 K) (i : Fin n) :
    reduce P x i = Ideal.Quotient.mk P.1 (x i) := rfl

/- [paper, equation `eq:def_of_L`, lines 1816--1827] The Grassmannian of
`s`-dimensional `k_𝓟`-subspaces of `k_𝓟^n`. -/
abbrev Code (P : PrimeIdeal K) (n s : ℕ) :=
  {S : Submodule (residueField P) (Fin n → residueField P) //
    Module.finrank (residueField P) S = s}

/- [derived consequence of paper equation `eq:def_of_L`, lines 1816--1827]
There are finitely many codes because `k_𝓟^n` is a finite vector space.
   This is the finiteness needed to interpret the paper's uniform average over
   `𝓛(𝓟,s)` once the averaging functional is introduced. -/
noncomputable instance code.finite (P : PrimeIdeal K) (n s : ℕ) :
    Finite (Code P n s) := by
  infer_instance

noncomputable instance code.fintype (P : PrimeIdeal K) (n s : ℕ) :
    Fintype (Code P n s) := Fintype.ofFinite _

/- [paper, equation `eq:def_of_L`, lines 1816--1827] The full preimage of a
code under reduction.  This is the unscaled lift
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

/- [Lean infrastructure for paper equation `eq:def_of_L`, lines 1816--1827]
Membership in the full inverse image is definitionally reduction into the
code. -/
theorem mem_rawLift_iff (P : PrimeIdeal K) {n s : ℕ} (S : Code P n s)
    (x : Fin n → 𝓞 K) :
    x ∈ rawLift P S ↔ reduce P x ∈ S.1 := Iff.rfl

/- [paper, equation `eq:def_of_L`, lines 1816--1827] The coordinatewise copy
of `𝓟` inside `𝓞 K^n`, corresponding to
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

/- [derived consequence of paper equation `eq:def_of_L`, lines 1816--1827]
The lower member of the manuscript's sandwich lies in every raw lift. -/
theorem primePowerVectors_le_rawLift (P : PrimeIdeal K)
    {n s : ℕ} (S : Code P n s) :
    primePowerVectors P n ≤ rawLift P S := by
  intro x hx
  change reduce P x ∈ S.1
  rw [show reduce P x = 0 by
    ext i
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hx i)]
  exact S.1.zero_mem

/- [Lean infrastructure for paper equation `eq:def_of_L`, lines 1816--1827]
Coordinatewise canonical embedding into `K_ℝ`. -/
noncomputable def embedVector (x : Fin n → 𝓞 K) : Fin n → K_ℝ[K] :=
  fun i => numberEmbedding K (x i)

/- [paper, equation `eq:def_of_L`, lines 1816--1827]
`T_𝓟 = N(𝓟)^((1-s/n)/d)`.  We use `Real.rpow`
   because the exponent is generally real. -/
noncomputable def liftScale (P : PrimeIdeal K) (n s : ℕ) : ℝ :=
  Real.rpow (idealNorm P : ℝ)
    ((1 - (s : ℝ) / (n : ℝ)) / (degree K : ℝ))

/- [derived consequence of paper equation `eq:def_of_L`, lines 1816--1827]
The manuscript's normalizing scale is positive. -/
theorem liftScale_pos (P : PrimeIdeal K) (n s : ℕ) :
    0 < liftScale P n s := by
  rw [liftScale]
  apply Real.rpow_pos_of_pos
  have hnorm : idealNorm P ≠ 0 := by
    intro hzero
    apply P.2.2
    exact Ideal.absNorm_eq_zero_iff.mp hzero
  exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hnorm)

/- [derived consequence of paper equation `eq:def_of_L`, lines 1816--1827]
The scale has exactly the normalization used in
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

/- [paper, equation `eq:def_of_L`, lines 1816--1827] The normalized lattice
`T_𝓟⁻¹ Λ` associated to a code. -/
noncomputable def normalizedLift (P : PrimeIdeal K) {n s : ℕ} (S : Code P n s) :
    Set (Fin n → K_ℝ[K]) :=
  (fun x => (liftScale P n s)⁻¹ • embedVector x) '' (rawLift P S : Set (Fin n → 𝓞 K))

/- [Lean infrastructure for paper equation `eq:def_of_L`, lines 1816--1827]
Unfolded membership in a normalized lift. -/
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

/- [Lean infrastructure for paper equation `eq:def_of_L`, lines 1816--1827]
Reduction `𝓞_K^n → k_𝓟^n` is surjective coordinatewise.  This is the basic
fact needed to recover a code from its full inverse-image lattice. -/
theorem reduce_surjective (P : PrimeIdeal K) (n : ℕ) :
    Function.Surjective (@reduce K _ _ P n) := by
  intro y
  choose x hx using fun i : Fin n => Ideal.Quotient.mk_surjective (y i)
  refine ⟨x, ?_⟩
  funext i
  exact hx i

/- [derived consequence of paper equation `eq:def_of_L`, lines 1816--1827]
Distinct residue-field codes have distinct unscaled inverse-image lattices.
Thus indexing the construction by codes introduces no multiplicity. -/
theorem rawLift_injective (P : PrimeIdeal K) {n s : ℕ} :
    Function.Injective (@rawLift K _ _ P n s) := by
  intro S S' hraw
  apply Subtype.ext
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx⟩ := reduce_surjective P n y
    have hxS : x ∈ rawLift P S := by
      change reduce P x ∈ S.1
      rw [hx]
      exact hy
    have hxS' : x ∈ rawLift P S' := by
      rw [← hraw]
      exact hxS
    change reduce P x ∈ S'.1 at hxS'
    rwa [hx] at hxS'
  · intro y hy
    obtain ⟨x, hx⟩ := reduce_surjective P n y
    have hxS' : x ∈ rawLift P S' := by
      change reduce P x ∈ S'.1
      rw [hx]
      exact hy
    have hxS : x ∈ rawLift P S := by
      rw [hraw]
      exact hxS'
    change reduce P x ∈ S.1 at hxS
    rwa [hx] at hxS

/- [Lean infrastructure for paper equation `eq:def_of_L`, lines 1816--1827]
The coordinatewise canonical embedding of integral vectors is injective. -/
theorem embedVector_injective {n : ℕ} :
    Function.Injective (@embedVector K _ _ n) := by
  intro x y hxy
  funext i
  apply NumberField.RingOfIntegers.coe_injective
  exact numberEmbedding_injective K (congrFun hxy i)

/- [derived consequence of paper equation `eq:def_of_L`, lines 1816--1827]
The normalized lift still determines its code: canonical embedding and scaling
are injective, and the preceding theorem recovers the code from the raw lift.
This is the proved bridge that identifies the code index with the manuscript's
finite family of actual normalized lattices. -/
theorem normalizedLift_injective (P : PrimeIdeal K) {n s : ℕ} :
    Function.Injective (@normalizedLift K _ _ P n s) := by
  intro S S' hnormalized
  let c : ℝ := (liftScale P n s)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (ne_of_gt (liftScale_pos P n s))
  have hmap : Function.Injective
      (fun x : Fin n → 𝓞 K => c • embedVector x) :=
    (smul_right_injective (Fin n → K_ℝ[K]) hc).comp embedVector_injective
  have himages :
      (fun x : Fin n → 𝓞 K => c • embedVector x) ''
          (rawLift P S : Set (Fin n → 𝓞 K)) =
        (fun x : Fin n → 𝓞 K => c • embedVector x) ''
          (rawLift P S' : Set (Fin n → 𝓞 K)) := by
    simpa [normalizedLift, c] using hnormalized
  have hrawSets : (rawLift P S : Set (Fin n → 𝓞 K)) =
      (rawLift P S' : Set (Fin n → 𝓞 K)) :=
    (Set.image_injective.mpr hmap) himages
  apply rawLift_injective P
  exact SetLike.ext' hrawSets

/- [Lean infrastructure for paper equation `eq:def_of_L`, lines 1816--1827]
The image of an intermediate `𝓞_K`-submodule under reduction.  Because every
residue-field scalar has an integral lift, this image is a residue-field
subspace.  It is the concrete realization of the quotient
`Λ / (𝓟𝓞_K)^n` used in the manuscript. -/
noncomputable def reducedIntermediateModule (P : PrimeIdeal K) {n : ℕ}
    (Λ : Submodule (𝓞 K) (Fin n → 𝓞 K)) :
    Submodule (residueField P) (Fin n → residueField P) where
  carrier := reduce P '' (Λ : Set (Fin n → 𝓞 K))
  zero_mem' := by
    refine ⟨0, Λ.zero_mem, ?_⟩
    ext i
    simp [reduce]
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    refine ⟨x + y, Λ.add_mem hx hy, ?_⟩
    ext i
    simp [reduce]
  smul_mem' := by
    rintro a _ ⟨x, hx, rfl⟩
    obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨a₀ • x, Λ.smul_mem a₀ hx, ?_⟩
    ext i
    simp [reduce, Pi.smul_apply]

/- [derived consequence of paper equation `eq:def_of_L`, lines 1816--1827]
Reducing the full inverse image of a code recovers that code exactly. -/
theorem reducedIntermediateModule_rawLift_eq
    (P : PrimeIdeal K) {n s : ℕ} (S : Code P n s) :
    reducedIntermediateModule P (rawLift P S) = S.1 := by
  apply Submodule.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    obtain ⟨x, hx⟩ := reduce_surjective P n y
    refine ⟨x, ?_, hx⟩
    change reduce P x ∈ S.1
    simpa [hx] using hy

/- [derived consequence of paper equation `eq:def_of_L`, lines 1816--1827]
Conversely, an intermediate module containing `(𝓟𝓞_K)^n` is the full inverse
image of its reduction.  This is the exact sandwich/quotient correspondence
used by the manuscript, rather than a cardinality argument. -/
theorem rawLift_reducedIntermediateModule_eq
    (P : PrimeIdeal K) {n s : ℕ}
    (Λ : Submodule (𝓞 K) (Fin n → 𝓞 K))
    (hlower : primePowerVectors P n ≤ Λ)
    (hrank : Module.finrank (residueField P)
      (reducedIntermediateModule P Λ) = s) :
    rawLift P (⟨reducedIntermediateModule P Λ, hrank⟩ : Code P n s) = Λ := by
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    change reduce P x ∈ reducedIntermediateModule P Λ at hx
    rcases hx with ⟨y, hy, hyx⟩
    have hxy : x - y ∈ primePowerVectors P n := by
      intro i
      have hi := congrFun hyx i
      have hzero : Ideal.Quotient.mk P.1 (x i - y i) = 0 := by
        rw [map_sub]
        change reduce P x i - reduce P y i = 0
        rw [hi]
        simp
      exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
    have hdiff : x - y ∈ Λ := hlower hxy
    have hadd := Λ.add_mem hdiff hy
    simpa using hadd
  · intro hx
    exact ⟨x, hx, rfl⟩

/- [Lean infrastructure for paper equation `eq:def_of_L`, lines 1816--1827]
Normalize an arbitrary intermediate module by the manuscript's scalar
`T_𝓟⁻¹`. -/
noncomputable def normalizedIntermediateModule (P : PrimeIdeal K) {n s : ℕ}
    (Λ : Submodule (𝓞 K) (Fin n → 𝓞 K)) : Set (Fin n → K_ℝ[K]) :=
  (fun x => (liftScale P n s)⁻¹ • embedVector x) ''
    (Λ : Set (Fin n → 𝓞 K))

/- [paper, equation `eq:def_of_L`, lines 1816--1827] This is the literal
set-builder in the manuscript: the lower inclusion is recorded explicitly,
the upper inclusion is inherent in `Λ ≤ 𝓞_K^n`, and the reduction image is
required to be an `s`-plane. -/
noncomputable def literalLifts (K : Type*) [Field K] [NumberField K]
    (P : PrimeIdeal K) (n s : ℕ) : Set (Set (Fin n → K_ℝ[K])) :=
  {L | ∃ Λ : Submodule (𝓞 K) (Fin n → 𝓞 K),
    primePowerVectors P n ≤ Λ ∧
      Module.finrank (residueField P) (reducedIntermediateModule P Λ) = s ∧
      L = normalizedIntermediateModule P (s := s) Λ}

/- [derived consequence of paper equation `eq:def_of_L`, lines 1816--1827]
The literal sandwich/quotient family is exactly the range of normalized code
lifts.  This theorem is the bridge permitting the later finite-field argument
to use codes as a multiplicity-free index. -/
theorem literalLifts_eq_range_normalizedLift
    (P : PrimeIdeal K) (n s : ℕ) :
    literalLifts K P n s = Set.range (@normalizedLift K _ _ P n s) := by
  ext L
  constructor
  · rintro ⟨Λ, hlower, hrank, rfl⟩
    let S : Code P n s := ⟨reducedIntermediateModule P Λ, hrank⟩
    refine ⟨S, ?_⟩
    unfold normalizedLift normalizedIntermediateModule
    rw [rawLift_reducedIntermediateModule_eq P Λ hlower hrank]
  · rintro ⟨S, rfl⟩
    refine ⟨rawLift P S, primePowerVectors_le_rawLift P S, ?_, ?_⟩
    · rw [reducedIntermediateModule_rawLift_eq]
      exact S.2
    · rfl

/- [paper, equation `eq:def_of_L`, lines 1816--1827] The finite collection
`𝓛(𝓟,s)` is definitionally the manuscript's literal sandwich/quotient family.
Its equality with the range of normalized code lifts is the preceding proved
theorem, not part of this abbreviation. -/
abbrev Lifts (K : Type*) [Field K] [NumberField K]
    (P : PrimeIdeal K) (n s : ℕ) :=
  literalLifts K P n s

notation "𝓛[" K "," P "," n "," s "]" => Lifts K P n s

/- [Lean infrastructure for paper equation `eq:def_of_L`, lines 1816--1827]
The proved injectivity above gives an equivalence between codes and the
manuscript's family of normalized lifts. -/
noncomputable def codeEquivLifts (P : PrimeIdeal K) (n s : ℕ) :
    Code P n s ≃ 𝓛[K, P, n, s] :=
  Equiv.ofBijective
    (fun S : Code P n s =>
      ⟨normalizedLift P S, by
        change normalizedLift P S ∈ literalLifts K P n s
        rw [literalLifts_eq_range_normalizedLift]
        exact ⟨S, rfl⟩⟩)
    ⟨fun S S' h => normalizedLift_injective P (congrArg Subtype.val h), by
      intro L
      have hL : L.1 ∈ Set.range (@normalizedLift K _ _ P n s) := by
        rw [← literalLifts_eq_range_normalizedLift]
        exact (show L.1 ∈ literalLifts K P n s from L.2)
      rcases hL with ⟨S, hS⟩
      refine ⟨S, ?_⟩
      apply Subtype.ext
      exact hS⟩

/- [derived consequence of the preceding code--lift equivalence] The unique
code attached to a member of `𝓛(𝓟,s)` has dimension `s`. -/
theorem code_rank (P : PrimeIdeal K) {n s : ℕ} (Λ : 𝓛[K, P, n, s]) :
    Module.finrank (residueField P) ((codeEquivLifts P n s).symm Λ).1 = s :=
  ((codeEquivLifts P n s).symm Λ).2

/- [Lean infrastructure for the finite average in paper equation
`eq:nthmoment`, lines 1828--1836] Transport the finite code index across the
proved code--lift equivalence. -/
noncomputable instance lifts.fintype (P : PrimeIdeal K) (n s : ℕ) :
    Fintype 𝓛[K, P, n, s] :=
  Fintype.ofEquiv (Code P n s) (codeEquivLifts P n s)

/- [Lean infrastructure for paper equation `eq:nthmoment`, lines 1828--1836]
Matrices in `Λ^m`, represented by integral matrices whose columns lie in
   the raw lift.  This is the matrix form of the inner sum in (eq:nthmoment). -/
def matricesInLift (P : PrimeIdeal K) {n m s : ℕ} (S : Code P n s) :
    Set (IntegralMatrix K n m) :=
  {A | ∀ j, (fun i => A i j) ∈ rawLift P S}

/- [Lean infrastructure for paper equation `eq:nthmoment`, lines 1828--1836]
Unfolded membership in the integral matrix realization of `Λ^m`. -/
theorem mem_matricesInLift_iff (P : PrimeIdeal K) {n m s : ℕ}
    (S : Code P n s) (A : IntegralMatrix K n m) :
    A ∈ matricesInLift P S ↔
      ∀ j, (fun i => A i j) ∈ rawLift P S := Iff.rfl

/- [paper, equation `eq:nthmoment`, lines 1828--1836] For an actual
normalized lift `Λ`, this is the manuscript's Cartesian power `Λ^m`, written
as an `n × m` matrix whose columns belong to `Λ`. -/
def matricesInNormalizedLift {n m : ℕ}
    (Λ : Set (Fin n → K_ℝ[K])) : Set (M n m (K_ℝ[K])) :=
  {B | ∀ j, (fun i => B i j) ∈ Λ}

/- [Lean infrastructure for paper equations `eq:def_of_L` and
`eq:nthmoment`, lines 1816--1836] Apply the canonical embedding and the
normalizing scalar entrywise.  The codomain records the literal condition
that every column belongs to the normalized lift. -/
noncomputable def integralMatrixToNormalizedLift
    (P : PrimeIdeal K) {n m s : ℕ} (S : Code P n s) :
    {A : IntegralMatrix K n m // A ∈ matricesInLift P S} →
      {B : M n m (K_ℝ[K]) //
        B ∈ matricesInNormalizedLift (normalizedLift P S)} :=
  fun A => ⟨(liftScale P n s)⁻¹ • embedMatrix A.1, by
    intro j
    refine ⟨(fun i => A.1 i j), A.2 j, ?_⟩
    rfl⟩

/- [Lean infrastructure for paper equations `eq:def_of_L` and
`eq:nthmoment`, lines 1816--1836] The preceding map is injective. -/
theorem integralMatrixToNormalizedLift_injective
    (P : PrimeIdeal K) {n m s : ℕ} (S : Code P n s) :
    Function.Injective (integralMatrixToNormalizedLift P (m := m) S) := by
  intro A A' hAA'
  have hscale : (liftScale P n s)⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (liftScale_pos P n s))
  have hembed : embedMatrix A.1 = embedMatrix A'.1 :=
    (smul_right_injective (M n m (K_ℝ[K])) hscale)
      (congrArg Subtype.val hAA')
  apply Subtype.ext
  funext i j
  apply NumberField.RingOfIntegers.coe_injective
  exact numberEmbedding_injective K (congrFun (congrFun hembed i) j)

/- [derived consequence of paper equations `eq:def_of_L` and
`eq:nthmoment`, lines 1816--1836] Every matrix in the literal Cartesian power
of a normalized lift has a unique integral representative in the raw lift. -/
theorem integralMatrixToNormalizedLift_surjective
    (P : PrimeIdeal K) {n m s : ℕ} (S : Code P n s) :
    Function.Surjective (integralMatrixToNormalizedLift P (m := m) S) := by
  intro B
  have hcolumns : ∀ j : Fin m,
      ∃ y ∈ rawLift P S,
        (fun i => B.1 i j) = (liftScale P n s)⁻¹ • embedVector y := by
    intro j
    exact (mem_normalizedLift_iff P S (fun i => B.1 i j)).mp (B.2 j)
  choose y hyRaw hyColumn using hcolumns
  let A : IntegralMatrix K n m := fun i j => y j i
  have hA : A ∈ matricesInLift P S := by
    intro j
    exact hyRaw j
  refine ⟨⟨A, hA⟩, ?_⟩
  apply Subtype.ext
  funext i j
  exact (congrFun (hyColumn j) i).symm

/- [derived consequence of paper equations `eq:def_of_L` and
`eq:nthmoment`, lines 1816--1836] This equivalence is the explicit bridge
between the integral representatives used in the proof and the manuscript's
literal `Λ^m` indexing. -/
noncomputable def integralMatrixEquivNormalizedLift
    (P : PrimeIdeal K) {n m s : ℕ} (S : Code P n s) :
    {A : IntegralMatrix K n m // A ∈ matricesInLift P S} ≃
      {B : M n m (K_ℝ[K]) //
        B ∈ matricesInNormalizedLift (normalizedLift P S)} :=
  Equiv.ofBijective (integralMatrixToNormalizedLift P (m := m) S)
    ⟨integralMatrixToNormalizedLift_injective P (m := m) S,
      integralMatrixToNormalizedLift_surjective P (m := m) S⟩

/- [paper, equation `eq:nthmoment`, lines 1828--1836] The inner lattice sum
over the literal Cartesian power `Λ^m`. -/
noncomputable def normalizedLiftMatrixSum {n m : ℕ}
    (Λ : Set (Fin n → K_ℝ[K])) (f : M n m (K_ℝ[K]) → ℝ) : ℝ :=
  ∑' B : {B : M n m (K_ℝ[K]) // B ∈ matricesInNormalizedLift Λ}, f B.1

/- [Lean infrastructure for paper equation `eq:nthmoment`, lines 1828--1836]
The code-indexed realization of one lattice sum, with the normalization from
`normalizedLift`.  Its equality with the literal Cartesian-power sum is
proved immediately below. -/
noncomputable def liftCodeSum (P : PrimeIdeal K) {n m s : ℕ}
    (S : Code P n s) (f : M n m (K_ℝ[K]) → ℝ) : ℝ :=
  ∑' A : {A : IntegralMatrix K n m // A ∈ matricesInLift P S},
    f ((liftScale P n s)⁻¹ • embedMatrix A.1)

/- [derived consequence of paper equations `eq:def_of_L` and
`eq:nthmoment`, lines 1816--1836] The code-indexed inner sum used by the
finite-field calculation is exactly the manuscript's sum over `Λ^m`. -/
theorem liftCodeSum_eq_normalizedLiftMatrixSum
    (P : PrimeIdeal K) {n m s : ℕ} (S : Code P n s)
    (f : M n m (K_ℝ[K]) → ℝ) :
    liftCodeSum P S f = normalizedLiftMatrixSum (normalizedLift P S) f := by
  exact (integralMatrixEquivNormalizedLift P S).tsum_eq
    (fun B => f B.1)

/- [Lean infrastructure for paper equation `eq:nthmoment`, lines 1828--1836]
The finite average over `𝓛(𝓟,s)`, represented temporarily by its equivalent
code index. -/
noncomputable def liftsMoment (P : PrimeIdeal K) (n m s : ℕ)
    (f : M n m (K_ℝ[K]) → ℝ) : ℝ :=
  (Fintype.card (Code P n s) : ℝ)⁻¹ *
    ∑ S : Code P n s, liftCodeSum P S f

/- [paper, equation `eq:nthmoment`, lines 1828--1836] This is the literal
finite average over the actual family `𝓛(𝓟,s)` and the actual Cartesian
powers `Λ^m` occurring in the manuscript. -/
noncomputable def manuscriptLiftsMoment (P : PrimeIdeal K) (n m s : ℕ)
    (f : M n m (K_ℝ[K]) → ℝ) : ℝ :=
  (Fintype.card 𝓛[K, P, n, s] : ℝ)⁻¹ *
    ∑ Λ : 𝓛[K, P, n, s], normalizedLiftMatrixSum Λ.1 f

/- [derived consequence of paper equation `eq:nthmoment`, lines 1828--1836]
The literal manuscript average agrees with the code-indexed form used for the
finite-field expansion.  Both changes of index are supplied by proved
equivalences above. -/
theorem manuscriptLiftsMoment_eq_liftsMoment
    (P : PrimeIdeal K) (n m s : ℕ)
    (f : M n m (K_ℝ[K]) → ℝ) :
    manuscriptLiftsMoment P n m s f = liftsMoment P n m s f := by
  rw [manuscriptLiftsMoment, liftsMoment]
  have hcard : Fintype.card 𝓛[K, P, n, s] =
      Fintype.card (Code P n s) :=
    Fintype.card_congr (codeEquivLifts P n s).symm
  rw [hcard]
  congr 1
  rw [← (codeEquivLifts P n s).sum_comp]
  apply Finset.sum_congr rfl
  intro S _
  exact (liftCodeSum_eq_normalizedLiftMatrixSum P S f).symm

end
end Katznelson
