import Katznelson.MainTheorems
import Mathlib.Analysis.Matrix.Normed

/-!
# Katznelson formalization

This project formalizes `papers/katznelson.tex`, the checked-in source of the
preprint *Integral matrices of fixed rank over number fields* (arXiv:2510.11673).
The TeX source is authoritative; the arXiv handle is included for reference.
-/

namespace Katznelson

open scoped Classical

/- Use the Frobenius norm for the paper's Euclidean matrix space. -/
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

/-!
## Main counting theorem

This is Theorem `th:main` of `papers/katznelson.tex`: for an admissible
function on `M_{n × m}(K_ℝ)`, the rank-k integral-matrix sum has order
`T^(k*n*d)`, with normalized additive error bounded by `T⁻¹ log T`.
Unless `d = k = 1` and `m = n - 1`, the logarithm can be dropped.
-/
theorem fixed_rank_count
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (h_dimensions : n > m ∧ m ≥ k ∧ k ≥ 1)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f) :
    ∃ cMain cError : ℝ, 0 < cError ∧
      (∀ T : ℝ, 2 ≤ T →
          |fixedRankSum n m k f T / T ^ (k * n * degree K) - cMain| ≤
            cError * T⁻¹ * Real.log T) ∧
      (¬(degree K = 1 ∧ k = 1 ∧ m = n - 1) →
        ∀ T : ℝ, 2 ≤ T →
          |fixedRankSum n m k f T / T ^ (k * n * degree K) - cMain| ≤
            cError * T⁻¹) := by
  sorry

/-!
## Main lifts-of-codes theorem

This is Theorem `th:higher_moments`: for the permitted `s`, the m-th moment
over `𝓛(𝓟,s)` converges as `𝓝(𝓟) → ∞` to the echelon-matrix integral sum.
-/
theorem lifts_of_codes_convergence
    {K : Type*} [Field K] [NumberField K]
    {n m s : ℕ} (h_n : 2 ≤ n) (h_m : 1 ≤ m ∧ m < n)
    (h_s : s = n - 1 ∨ (m ≤ s ∧ s < n ∧ m * (n - s) < n))
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f) :
    tendsToAtNorm
      (fun P => liftsMoment P n m s f)
      (echelonIntegralLimit n m s f) := by
  sorry

end Katznelson
