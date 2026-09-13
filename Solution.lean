import main

/-!
# Palomar solution surface

This file gives the proved counterparts of the declarations in
`Challenge.lean`.  The aliases preserve the exact Challenge names and types,
while the theorem bodies call the completed public development.
-/

noncomputable section

open Filter
open scoped Classical NumberField Topology

namespace Katznelson.Palomar

universe u

abbrev M (n m : ℕ) (R : Type*) := Katznelson.M n m R

abbrev KReal (K : Type u) [Field K] [NumberField K] := Katznelson.KReal K

abbrev degree (K : Type u) [Field K] [NumberField K] : ℕ := Katznelson.degree K

abbrev Admissible {K : Type u} [Field K] [NumberField K] {n m : ℕ}
    (f : M n m (KReal K) → ℝ) : Prop := Katznelson.Admissible f

abbrev HasHeightCountBounds {α : Type*} (H : α → ℝ) (p : ℕ) : Prop :=
  Katznelson.HasHeightCountBounds H p

abbrev RowSpace (K : Type u) [Field K] [NumberField K] (m k : ℕ) : Type u :=
  Katznelson.Grassmannian K m k

abbrev rowSpaceHeight {K : Type u} [Field K] [NumberField K]
    {m k : ℕ} (V : RowSpace K m k) : ℝ := Katznelson.rowSpaceHeight V

abbrev fixedRankSum {K : Type u} [Field K] [NumberField K]
    (n m k : ℕ) (f : M n m (KReal K) → ℝ) (T : ℝ) : ℝ :=
  Katznelson.fixedRankSum n m k f T

abbrev mainConstant {K : Type u} [Field K] [NumberField K]
    (n m k : ℕ) (f : M n m (KReal K) → ℝ) : ℝ :=
  Katznelson.mainConstant n m k f

abbrev PrimeIdeal (K : Type u) [Field K] [NumberField K] : Type u :=
  Katznelson.PrimeIdeal K

abbrev liftScale {K : Type u} [Field K] [NumberField K]
    (P : PrimeIdeal K) (n s : ℕ) : ℝ := Katznelson.liftScale P n s

abbrev manuscriptLiftsMoment {K : Type u} [Field K] [NumberField K]
    (P : PrimeIdeal K) (n m s : ℕ)
    (f : M n m (KReal K) → ℝ) : ℝ :=
  Katznelson.manuscriptLiftsMoment P n m s f

abbrev manuscriptEchelonIntegralLimit {K : Type u} [Field K] [NumberField K]
    (n m : ℕ) (f : M n m (KReal K) → ℝ) : ℝ :=
  Katznelson.manuscriptEchelonIntegralLimit n m f

abbrev tendsToAtNorm {K : Type u} [Field K] [NumberField K]
    (F : PrimeIdeal K → ℝ) (limit : ℝ) : Prop := Katznelson.tendsToAtNorm F limit

theorem fixed_rank_count
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (h_dimensions : n > m ∧ m ≥ k ∧ k ≥ 1)
    (f : M n m (KReal K) → ℝ) (h_f : Admissible f)
    (hcount : ∀ l : ℕ, 1 ≤ l → l ≤ k → l < m →
      HasHeightCountBounds
        (rowSpaceHeight (K := K) (m := m) (k := l)) m) :
    ∃ cMain cError : ℝ, 0 < cError ∧
      cMain = mainConstant n m k f ∧
      (∀ T : ℝ, 2 ≤ T →
          |fixedRankSum n m k f T / T ^ (k * n * degree K) - cMain| ≤
            cError * T⁻¹ * Real.log T) ∧
      (¬(degree K = 1 ∧ k = 1 ∧ m = n - 1) →
        ∀ T : ℝ, 2 ≤ T →
          |fixedRankSum n m k f T / T ^ (k * n * degree K) - cMain| ≤
            cError * T⁻¹) := by
  exact Katznelson.fixed_rank_count h_dimensions f h_f hcount

theorem lifts_of_codes_convergence
    {K : Type*} [Field K] [NumberField K]
    {n m s : ℕ} (h_n : 2 ≤ n) (h_m : 1 ≤ m ∧ m < n)
    (h_s : s = n - 1 ∨ (m ≤ s ∧ s < n ∧ m * (n - s) < n))
    (f : M n m (KReal K) → ℝ) (h_f : Admissible f)
    (hcount : ∀ l : ℕ, 1 ≤ l → l < m →
      HasHeightCountBounds
        (rowSpaceHeight (K := K) (m := m) (k := l)) m) :
    tendsToAtNorm
      (fun P : PrimeIdeal K =>
        manuscriptLiftsMoment P n m s f)
      (manuscriptEchelonIntegralLimit (K := K) n m f) := by
  exact Katznelson.lifts_of_codes_convergence h_n h_m h_s f h_f hcount

end Katznelson.Palomar
