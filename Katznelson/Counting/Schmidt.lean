import Katznelson.Counting.RowLattice
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Height counting for rational row spaces

The manuscript uses the height-counting theorem for rational subspaces to
control echelon-matrix tails.  This file fixes the Lean interface for that
input.  Its mathematical source is W. M. Schmidt, *On Heights of Algebraic
Subspaces and Diophantine
Approximations*, Ann. of Math. (2) 85 (1967), Theorem 3 (p. 440).  J. L.
Thunder, *An Asymptotic Estimate for Heights of Algebraic Subspaces*, Trans.
Amer. Math. Soc. 331 (1992), Theorem 1 (p. 395), proves a sharper asymptotic
for the same count.  Thunder is recorded here as a refinement, not as a
second attribution of Schmidt’s original argument.

   The row-space and covolume definitions used in the statement are new Lean
   infrastructure corresponding to Definition `de:height_definition` and the
   row-space discussion in lines 758--815 of `papers/katznelson.tex`.  The
   current Lean row representation uses an equivalent finite-dimensional norm;
   for fixed `K`, norm equivalence changes only the constants in the count,
   not the exponent `m`.
-/

namespace Katznelson

open Set
open Filter
open MeasureTheory
open scoped Classical NumberField Topology

section

variable {K : Type*} [Field K] [NumberField K]

/- [Lean infrastructure] Height cutoff for the Grassmannian representation of
   the paper's rational-subspace count. -/
def rowSpaceHeightBall {m k : ℕ} (T : ℝ) : Set (Grassmannian K m k) :=
  {V | rowSpaceHeight V ≤ T}

/- This is the height-cutoff family corresponding to the manuscript's crude
   estimate `H(D) ≤ C T^(k d)` (lines 1091--1100).  The identification of the
   norm-bounded support family with this height cutoff is a separate geometry-
   of-numbers step; this definition keeps that step explicit. -/
/- [Lean infrastructure] Grassmannian form of the height cutoff appearing
   after the paper's crude support bound. -/
def heightBoundedRowSpaces {m k : ℕ} (C T : ℝ) :
    Set (Grassmannian K m k) :=
  rowSpaceHeightBall (m := m) (k := k) (C * T ^ (k * degree K))

/- [Lean infrastructure] Explicit predicate for the two-sided polynomial
   height-counting input.  This predicate is not an imported theorem and is
   not discharged by an axiom in this development. -/
def HasHeightCountBounds {α : Type*} (H : α → ℝ) (p : ℕ) : Prop :=
  ∃ cₗ cᵤ : ℝ, 0 < cₗ ∧ 0 < cᵤ ∧
    ∀ T : ℝ, 1 ≤ T →
      (Set.Finite {x | H x ≤ T}) ∧
        cₗ * T ^ p ≤ (Set.ncard {x | H x ≤ T} : ℝ) ∧
        (Set.ncard {x | H x ≤ T} : ℝ) ≤ cᵤ * T ^ p

/- [derived consequence, paper lines 649--653] This is the finite Abel
   summation identity used below.  It is recorded separately so the later
   estimate can be checked against the manuscript's summation-by-parts step. -/
theorem sum_Ico_inv_pow_by_parts
    {φ : ℕ → ℝ} {a b q : ℕ} (hab : a < b) :
    (∑ n ∈ Finset.Ico a b, φ n * ((n : ℝ)⁻¹ ^ q)) =
      ((b - 1 : ℕ) : ℝ)⁻¹ ^ q * (∑ n ∈ Finset.range b, φ n) -
        (a : ℝ)⁻¹ ^ q * (∑ n ∈ Finset.range a, φ n) -
        ∑ n ∈ Finset.Ico a (b - 1),
          ((((n + 1 : ℕ) : ℝ)⁻¹ ^ q - (n : ℝ)⁻¹ ^ q) *
            (∑ i ∈ Finset.range (n + 1), φ i)) := by
  simpa [smul_eq_mul, mul_comm] using
    (Finset.sum_Ico_by_parts
      (f := fun n : ℕ => ((n : ℝ)⁻¹ ^ q)) (g := φ) hab)

/- [derived consequence, paper lines 649--653] A quantitative ordinary-shell
   estimate in the endpoint convention used by Mathlib's Abel formula.  The
   cumulative bound is explicit: it is the formal counterpart of the paper's
   bound on `Phi`.  The integral is written with ordinary inverse powers; on
   positive arguments this is exactly the paper's `x^(h1-h2-1)` integrand. -/
set_option maxHeartbeats 800000 in
theorem sum_Ioc_inv_pow_le_of_partial_sum
    {φ : ℕ → ℝ} {C : ℝ} {a b p q : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hC : 0 ≤ C)
    (hφ : ∀ n : ℕ, 0 ≤ φ n)
    (hpartial : ∀ {n : ℕ}, 1 ≤ n →
      (∑ i ∈ Finset.Icc 0 n, φ i) ≤ C * (n : ℝ) ^ p) :
    (∑ n ∈ Finset.Ioc a b, φ n * ((n : ℝ)⁻¹ ^ q)) ≤
      C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) +
        C * (q : ℝ) *
          (∫ x in (a : ℝ)..(b : ℝ),
            x ^ p * (x⁻¹ ^ (q + 1))) := by
  let P : ℝ → ℝ := fun t => ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, φ i
  have hP_nonneg : ∀ t : ℝ, 0 ≤ P t := by
    intro t
    dsimp [P]
    exact Finset.sum_nonneg fun i hi => hφ i
  have hP_bound : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ),
      P t ≤ C * t ^ p := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := by
      exact le_trans (by exact_mod_cast ha) ht.1
    have hn1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).2 ht1
    have hpartial' := hpartial hn1
    have hfloor : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t :=
      Nat.floor_le (by positivity)
    have hpow : ((⌊t⌋₊ : ℕ) : ℝ) ^ p ≤ t ^ p :=
      pow_le_pow_left₀ (by positivity) hfloor p
    dsimp [P]
    exact (hpartial'.trans (mul_le_mul_of_nonneg_left hpow hC))
  let f : ℝ → ℝ := fun t => t ^ (-(q : ℝ))
  have hf_diff : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ),
      DifferentiableAt ℝ f t := by
    intro t ht
    dsimp [f]
    apply Real.differentiableAt_rpow_const_of_ne
    exact ne_of_gt (lt_of_lt_of_le (by exact_mod_cast ha) ht.1)
  have hderiv : deriv f = fun t : ℝ =>
      (-(q : ℝ)) * t ^ (-(q : ℝ) - 1) := by
    dsimp [f]
    exact Real.deriv_rpow_const' (-(q : ℝ))
  have hpow_cont : ContinuousOn
      (fun t : ℝ => t ^ (-(q : ℝ) - 1))
      (Set.Icc (a : ℝ) (b : ℝ)) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro t ht
    exact Or.inl (ne_of_gt (lt_of_lt_of_le (by exact_mod_cast ha) ht.1))
  have hf_int : IntegrableOn (deriv f)
      (Set.Icc (a : ℝ) (b : ℝ)) := by
    rw [hderiv]
    exact (continuousOn_const.mul hpow_cont).integrableOn_Icc
  have habel :=
    sum_mul_eq_sub_sub_integral_mul
      (c := φ) (f := f) (a := (a : ℝ)) (b := (b : ℝ))
      (by exact_mod_cast (Nat.zero_le a))
      (by exact_mod_cast hab) hf_diff hf_int
  have habel' :
      (∑ n ∈ Finset.Ioc a b, φ n * ((n : ℝ)⁻¹ ^ q)) =
        f (b : ℝ) * P (b : ℝ) - f (a : ℝ) * P (a : ℝ) -
          ∫ t in (a : ℝ)..(b : ℝ),
            (deriv f t) * P t := by
    rw [intervalIntegral.integral_of_le (by exact_mod_cast hab)]
    simpa [P, f, Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast,
      Nat.floor_natCast, mul_comm]
      using habel
  have hfa_nonneg : 0 ≤ f (a : ℝ) := by
    dsimp [f]
    positivity
  have hfb_nonneg : 0 ≤ f (b : ℝ) := by
    dsimp [f]
    positivity
  have hendpoint :
      f (b : ℝ) * P (b : ℝ) ≤
        C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) := by
    have hPb := hP_bound (b : ℝ) ⟨by exact_mod_cast hab, le_rfl⟩
    calc
      f (b : ℝ) * P (b : ℝ) ≤ f (b : ℝ) * (C * (b : ℝ) ^ p) :=
        mul_le_mul_of_nonneg_left hPb hfb_nonneg
      _ = C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) := by
        dsimp [f]
        rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
        ring
  have hnegendpoint : -f (a : ℝ) * P (a : ℝ) ≤ 0 := by
    simpa only [neg_mul] using
      (neg_nonpos.mpr (mul_nonneg hfa_nonneg (hP_nonneg (a : ℝ))))
  have hprod_int : IntegrableOn
      (fun t : ℝ => (q : ℝ) * t ^ (-(q : ℝ) - 1) * P t)
      (Set.Icc (a : ℝ) (b : ℝ)) := by
    have hmul : IntegrableOn (fun t : ℝ => deriv f t * P t)
        (Set.Icc (a : ℝ) (b : ℝ)) :=
      integrableOn_mul_sum_Icc (c := φ) (a := (a : ℝ)) (b := (b : ℝ))
        (by exact_mod_cast (Nat.zero_le a)) hf_int
    have hmul' := hmul.neg
    rw [hderiv] at hmul'
    convert hmul' using 1
    funext t
    simp only [Pi.neg_apply]
    rw [show -(q : ℝ) - 1 = -1 - (q : ℝ) by ring]
    ring
  have hmajor_cont : ContinuousOn
      (fun t : ℝ => C * (q : ℝ) * t ^ p * (t⁻¹ ^ (q + 1)))
      (Set.Icc (a : ℝ) (b : ℝ)) := by
    have hinv : ContinuousOn (fun t : ℝ => t⁻¹)
        (Set.Icc (a : ℝ) (b : ℝ)) :=
      continuousOn_inv₀.mono (fun t ht =>
        ne_of_gt (lt_of_lt_of_le (by exact_mod_cast ha) ht.1))
    exact (continuousOn_const.mul (continuousOn_id.pow p)).mul
      (hinv.pow (q + 1))
  have hmajor_int : IntegrableOn
      (fun t : ℝ => C * (q : ℝ) * t ^ p * (t⁻¹ ^ (q + 1)))
      (Set.Icc (a : ℝ) (b : ℝ)) :=
    hmajor_cont.integrableOn_Icc
  have hpoint : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ),
      (q : ℝ) * t ^ (-(q : ℝ) - 1) * P t ≤
        C * (q : ℝ) * t ^ p * (t⁻¹ ^ (q + 1)) := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by exact_mod_cast ha) ht.1
    have hpow_inv : t ^ (-(q : ℝ) - 1) = t⁻¹ ^ (q + 1) := by
      rw [show -(q : ℝ) - 1 = -((q + 1 : ℕ) : ℝ) by
        push_cast
        ring]
      rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
    rw [hpow_inv]
    have h := hP_bound t ht
    have hmul :
        (q : ℝ) * t⁻¹ ^ (q + 1) * P t ≤
          (q : ℝ) * t⁻¹ ^ (q + 1) * (C * t ^ p) :=
      mul_le_mul_of_nonneg_left h
        (mul_nonneg (by positivity) (by positivity : 0 ≤ t⁻¹ ^ (q + 1)))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hintegral :
      (∫ t in (a : ℝ)..(b : ℝ),
          (q : ℝ) * t ^ (-(q : ℝ) - 1) * P t) ≤
        C * (q : ℝ) *
          (∫ t in (a : ℝ)..(b : ℝ), t ^ p * (t⁻¹ ^ (q + 1))) := by
    have hprod_interval : IntervalIntegrable
        (fun t : ℝ => (q : ℝ) * t ^ (-(q : ℝ) - 1) * P t)
        volume (a : ℝ) (b : ℝ) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le
        (by exact_mod_cast hab)]
      exact hprod_int
    have hmajor_interval : IntervalIntegrable
        (fun t : ℝ => C * (q : ℝ) * t ^ p * (t⁻¹ ^ (q + 1)))
        volume (a : ℝ) (b : ℝ) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le
        (by exact_mod_cast hab)]
      exact hmajor_int
    calc
      (∫ t in (a : ℝ)..(b : ℝ),
          (q : ℝ) * t ^ (-(q : ℝ) - 1) * P t) ≤
          ∫ t in (a : ℝ)..(b : ℝ),
            C * (q : ℝ) * t ^ p * (t⁻¹ ^ (q + 1)) :=
        intervalIntegral.integral_mono_on (by exact_mod_cast hab)
          hprod_interval hmajor_interval hpoint
      _ = C * (q : ℝ) *
          (∫ t in (a : ℝ)..(b : ℝ), t ^ p * (t⁻¹ ^ (q + 1))) := by
        calc
          (∫ t in (a : ℝ)..(b : ℝ),
              C * (q : ℝ) * t ^ p * (t⁻¹ ^ (q + 1))) =
              ∫ t in (a : ℝ)..(b : ℝ),
                (C * (q : ℝ)) * (t ^ p * (t⁻¹ ^ (q + 1))) := by
                  congr 1
                  funext t
                  ring
          _ = C * (q : ℝ) *
              (∫ t in (a : ℝ)..(b : ℝ), t ^ p * (t⁻¹ ^ (q + 1))) := by
                rw [intervalIntegral.integral_const_mul]
  have hnegint :
      -(∫ t in (a : ℝ)..(b : ℝ),
          deriv f t * P t) =
        ∫ t in (a : ℝ)..(b : ℝ),
          (q : ℝ) * t ^ (-(q : ℝ) - 1) * P t := by
    rw [hderiv]
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext t
    ring
  calc
    (∑ n ∈ Finset.Ioc a b, φ n * ((n : ℝ)⁻¹ ^ q)) =
        f (b : ℝ) * P (b : ℝ) - f (a : ℝ) * P (a : ℝ) -
          ∫ t in (a : ℝ)..(b : ℝ), deriv f t * P t := habel'
    _ = f (b : ℝ) * P (b : ℝ) - f (a : ℝ) * P (a : ℝ) +
          (-(∫ t in (a : ℝ)..(b : ℝ), deriv f t * P t)) := by ring
    _ = f (b : ℝ) * P (b : ℝ) - f (a : ℝ) * P (a : ℝ) +
          ∫ t in (a : ℝ)..(b : ℝ),
            (q : ℝ) * t ^ (-(q : ℝ) - 1) * P t := by rw [hnegint]
    _ ≤ f (b : ℝ) * P (b : ℝ) +
          ∫ t in (a : ℝ)..(b : ℝ),
            (q : ℝ) * t ^ (-(q : ℝ) - 1) * P t := by
      linarith [hnegendpoint]
    _ ≤ C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) +
          ∫ t in (a : ℝ)..(b : ℝ),
            (q : ℝ) * t ^ (-(q : ℝ) - 1) * P t := by
      gcongr
    _ ≤ C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) +
          C * (q : ℝ) *
            (∫ t in (a : ℝ)..(b : ℝ), t ^ p * (t⁻¹ ^ (q + 1))) := by
      gcongr

/- [derived consequence, paper lines 649--653] On a positive interval the
   ordinary-shell integrand has the expected elementary antiderivative.  This
   identity is used below to keep the three possible signs of `p - q`
   separate; in particular, it does not silently turn a bounded negative-
   exponent contribution into a decaying power. -/
theorem intervalIntegral_nat_power_inv_power
    {p q N : ℕ} (hN : 1 ≤ N) (hpq : p ≠ q) :
    (∫ x in (1 : ℝ)..(N : ℝ),
      x ^ p * (x⁻¹ ^ (q + 1))) =
      (((N : ℝ) ^ ((p : ℝ) - q) - 1) / ((p : ℝ) - q)) := by
  let r : ℝ := (p : ℝ) - q - 1
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpeq : (p : ℝ) ≠ q := by
    exact_mod_cast hpq
  have hpow : ∀ x ∈ Set.uIcc (1 : ℝ) (N : ℝ),
      x ^ p * (x⁻¹ ^ (q + 1)) = x ^ r := by
    intro x hx
    have hx' := hx
    rw [uIcc_of_le hNreal] at hx'
    have hxpos : 0 < x := by
      exact lt_of_lt_of_le zero_lt_one hx'.1
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_natCast,
      Real.inv_rpow hxpos.le, ← Real.rpow_neg hxpos.le,
      ← Real.rpow_add hxpos]
    congr 1
    push_cast
    ring
  rw [intervalIntegral.integral_congr hpow]
  rw [integral_rpow]
  · dsimp [r]
    have hdenom : (p : ℝ) - q ≠ 0 := sub_ne_zero.mpr hpeq
    simp only [Real.one_rpow]
    congr 1
    · congr 1
      push_cast
      ring
    · push_cast
      ring
  · right
    constructor
    · intro hr
      have hpqR : (p : ℝ) = q := by
        dsimp [r] at hr
        linarith
      exact hpeq (by exact_mod_cast hpqR)
    · exact notMem_uIcc_of_lt (by positivity) (by positivity)

/- [derived consequence, paper lines 649--653] The borderline case is the
   logarithmic integral in the manuscript's summation-by-parts estimate. -/
theorem intervalIntegral_nat_power_inv_power_eq_log
    {p N : ℕ} (hN : 1 ≤ N) :
    (∫ x in (1 : ℝ)..(N : ℝ),
      x ^ p * (x⁻¹ ^ (p + 1))) = Real.log (N : ℝ) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : ∀ x ∈ Set.uIcc (1 : ℝ) (N : ℝ),
      x ^ p * (x⁻¹ ^ (p + 1)) = x⁻¹ := by
    intro x hx
    have hx' := hx
    rw [uIcc_of_le hNreal] at hx'
    have hxpos : 0 < x := by
      exact lt_of_lt_of_le zero_lt_one hx'.1
    rw [← Real.rpow_natCast, ← Real.rpow_natCast,
      Real.inv_rpow hxpos.le, ← Real.rpow_neg hxpos.le,
      ← Real.rpow_add hxpos]
    congr 1
    have hexp : (p : ℝ) + -((p + 1 : ℕ) : ℝ) = -1 := by
      push_cast
      ring
    rw [hexp, Real.rpow_neg_one]
  rw [intervalIntegral.integral_congr hpow]
  simpa using (integral_inv_of_pos (a := (1 : ℝ)) (b := (N : ℝ))
    (by positivity) (by positivity))
/- [derived consequence, paper lines 649--653] The improper integral which
   occurs in the Abel estimate has the expected power-law bound.  Keeping
   this as a separate lemma makes the passage from finite summation by parts
   to a quantitative tail explicit; no dyadic decomposition is involved. -/
set_option maxHeartbeats 400000 in
theorem intervalIntegral_height_power_le
    {p q a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hpq : p < q) :
    (∫ x in (a : ℝ)..(b : ℝ),
      x ^ p * (x⁻¹ ^ (q + 1))) ≤
      ((a : ℝ) ^ (-((q - p : ℕ) : ℝ))) /
        ((q : ℝ) - (p : ℝ)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hqmp : 0 < q - p := by omega
  have hqmpR : (0 : ℝ) < (q : ℝ) - (p : ℝ) := by
    rw [← Nat.cast_sub hpq.le]
    exact_mod_cast hqmp
  let r : ℝ := (q - p : ℕ)
  let e : ℝ := -r - 1
  have he : e < -1 := by
    dsimp [e, r]
    have hqmpR' : (1 : ℝ) ≤ ((q - p : ℕ) : ℝ) := by
      exact_mod_cast hqmp
    linarith
  have hrewrite : ∀ x : ℝ, 0 < x →
      x ^ p * (x⁻¹ ^ (q + 1)) = x ^ e := by
    intro x hx
    have hcast : (p : ℝ) - (q + 1 : ℕ) = e := by
      dsimp [e, r]
      rw [Nat.cast_sub hpq.le]
      push_cast
      ring
    rw [← Real.rpow_natCast x p,
      ← Real.rpow_natCast (x⁻¹) (q + 1)]
    rw [Real.inv_rpow hx.le]
    rw [← Real.rpow_neg hx.le]
    rw [← Real.rpow_add hx]
    rw [← hcast]
    congr 1
  have hg_nonneg : ∀ x ∈ Set.Ioi (a : ℝ), 0 ≤ x ^ e := by
    intro x hx
    change (a : ℝ) < x at hx
    exact Real.rpow_nonneg (le_of_lt (haR.trans hx)) _
  have hg_int : IntegrableOn (fun x : ℝ => x ^ e)
      (Set.Ioi (a : ℝ)) := by
    exact integrableOn_Ioi_rpow_of_lt he haR
  have hgb_int : IntegrableOn (fun x : ℝ => x ^ e)
      (Set.Ioi (b : ℝ)) :=
    hg_int.mono_set (Set.Ioi_subset_Ioi (by exact_mod_cast hab))
  have hinterval :
      (∫ x in (a : ℝ)..(b : ℝ), x ^ e) ≤
        ∫ x in Set.Ioi (a : ℝ), x ^ e := by
    have hadd := intervalIntegral.integral_interval_add_Ioi
      (f := fun x : ℝ => x ^ e) hg_int hgb_int
    have htail : 0 ≤ ∫ x in Set.Ioi (b : ℝ), x ^ e :=
      integral_nonneg_of_ae (ae_restrict_mem measurableSet_Ioi |>.mono
        (fun x hx => hg_nonneg x (by
          change (b : ℝ) < x at hx
          exact lt_of_le_of_lt (by exact_mod_cast hab) hx)))
    linarith
  have heval := integral_Ioi_rpow_of_lt he haR
  have hpower :
      -((a : ℝ) ^ (e + 1)) / (e + 1) =
        ((a : ℝ) ^ (-((q - p : ℕ) : ℝ))) /
          ((q : ℝ) - (p : ℝ)) := by
    dsimp [e, r]
    rw [show -((q - p : ℕ) : ℝ) - 1 + 1 = -((q - p : ℕ) : ℝ) by ring]
    have hsub : (q : ℝ) - (p : ℝ) = ((q - p : ℕ) : ℝ) := by
      rw [Nat.cast_sub hpq.le]
    rw [hsub]
    field_simp [ne_of_gt hqmpR]
  calc
    (∫ x in (a : ℝ)..(b : ℝ), x ^ p * (x⁻¹ ^ (q + 1))) =
        ∫ x in (a : ℝ)..(b : ℝ), x ^ e := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxa : (a : ℝ) ≤ x := by
        rw [Set.uIcc_of_le (by exact_mod_cast hab)] at hx
        exact hx.1
      exact hrewrite x (lt_of_lt_of_le haR hxa)
    _ ≤ ∫ x in Set.Ioi (a : ℝ), x ^ e := hinterval
    _ = -((a : ℝ) ^ (e + 1)) / (e + 1) := heval
    _ = ((a : ℝ) ^ (-((q - p : ℕ) : ℝ))) /
          ((q : ℝ) - (p : ℝ)) := hpower

/- [derived consequence, paper lines 649--653 and corollary `co:tail`]
   Uniform finite-tail form of the preceding Abel estimate.  The endpoint
   term is controlled by the same cumulative count as the integral term, so
   the exponent remains `p - q` even in the borderline case `q = p + 1`. -/
set_option maxHeartbeats 800000 in
theorem sum_Ioc_inv_pow_tail_le_of_partial_sum
    {φ : ℕ → ℝ} {C : ℝ} {N b p q : ℕ}
    (hC : 0 < C) (hN : 1 ≤ N) (hNb : N ≤ b) (hpq : p < q)
    (hφ : ∀ n : ℕ, 0 ≤ φ n)
    (hpartial : ∀ {n : ℕ}, 1 ≤ n →
      (∑ i ∈ Finset.Icc 0 n, φ i) ≤ C * (n : ℝ) ^ p) :
    (∑ n ∈ Finset.Ioc N b, φ n * ((n : ℝ)⁻¹ ^ q)) ≤
      C * (1 + (q : ℝ) / ((q : ℝ) - (p : ℝ))) *
          ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := by
  have hmain := sum_Ioc_inv_pow_le_of_partial_sum
    (φ := φ) (C := C) (a := N) (b := b) (p := p) (q := q)
    hN hNb hC.le hφ hpartial
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNbR : (N : ℝ) ≤ b := by exact_mod_cast hNb
  have hBpos : (0 : ℝ) < (b : ℝ) := lt_of_lt_of_le hNpos hNbR
  have hqmp : 0 < q - p := by omega
  have hqmpR : (0 : ℝ) < (q : ℝ) - (p : ℝ) := by
    rw [← Nat.cast_sub hpq.le]
    exact_mod_cast hqmp
  have hendpoint_eq :
      (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) =
        (b : ℝ) ^ (-((q - p : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast (b : ℝ) p,
      ← Real.rpow_natCast ((b : ℝ)⁻¹) q,
      Real.inv_rpow hBpos.le, ← Real.rpow_neg hBpos.le,
      ← Real.rpow_add hBpos]
    congr 1
    rw [Nat.cast_sub hpq.le]
    ring
  have hendpoint_mono :
      (b : ℝ) ^ (-((q - p : ℕ) : ℝ)) ≤
        (N : ℝ) ^ (-((q - p : ℕ) : ℝ)) := by
    rw [Real.rpow_neg hBpos.le, Real.rpow_neg hNpos.le]
    apply (inv_le_inv₀ (Real.rpow_pos_of_pos hBpos _)
      (Real.rpow_pos_of_pos hNpos _)).2
    exact Real.rpow_le_rpow hNpos.le hNbR (by positivity)
  have hIntegral := intervalIntegral_height_power_le
    (p := p) (q := q) hN hNb hpq
  have hIntegral' :
      (∫ x in (N : ℝ)..(b : ℝ),
        x ^ p * (x⁻¹ ^ (q + 1))) ≤
      ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) /
        ((q : ℝ) - (p : ℝ)) := hIntegral
  calc
    (∑ n ∈ Finset.Ioc N b, φ n * ((n : ℝ)⁻¹ ^ q)) ≤
        C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) +
          C * (q : ℝ) *
            (∫ x in (N : ℝ)..(b : ℝ), x ^ p * (x⁻¹ ^ (q + 1))) := hmain
    _ = C * ((b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q)) +
          C * (q : ℝ) *
            (∫ x in (N : ℝ)..(b : ℝ), x ^ p * (x⁻¹ ^ (q + 1))) := by ring
    _ ≤ C * ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) +
          C * (q : ℝ) *
            (((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) /
              ((q : ℝ) - (p : ℝ))) := by
      gcongr
      · rw [hendpoint_eq]
        exact hendpoint_mono
    _ = C * (1 + (q : ℝ) / ((q : ℝ) - (p : ℝ))) *
          ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := by
      field_simp [ne_of_gt hqmpR]

/- [derived consequence, paper lines 649--653 and corollary `co:tail`]
   The preceding finite estimate gives the corresponding infinite ordinary-
   shell tail.  The proof uses the finite-subset characterization of a
   nonnegative real tsum; the only summation decomposition is the paper's
   unit-shell split into the endpoint `N` and `Ioc N b`. -/
set_option maxHeartbeats 1000000 in
theorem tsum_indicator_Ici_inv_pow_le_of_partial_sum
    {φ : ℕ → ℝ} {C : ℝ} {N p q : ℕ}
    (hC : 0 < C) (hN : 1 ≤ N) (hpq : p < q)
    (hφ : ∀ n : ℕ, 0 ≤ φ n)
    (hpartial : ∀ {n : ℕ}, 1 ≤ n →
      (∑ i ∈ Finset.Icc 0 n, φ i) ≤ C * (n : ℝ) ^ p) :
    (∑' n : ℕ, if N ≤ n then φ n * ((n : ℝ)⁻¹ ^ q) else 0) ≤
      C * (2 + (q : ℝ) / ((q : ℝ) - (p : ℝ))) *
        ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := by
  classical
  have hnonneg : ∀ n : ℕ,
      0 ≤ if N ≤ n then φ n * ((n : ℝ)⁻¹ ^ q) else 0 := by
    intro n
    by_cases h : N ≤ n
    · simp only [h, ↓reduceIte]
      exact mul_nonneg (hφ n) (by positivity)
    · simp only [h, ↓reduceIte]
      exact le_rfl
  have hqmp : 0 < q - p := by omega
  have hqmpR : (0 : ℝ) < (q : ℝ) - (p : ℝ) := by
    rw [← Nat.cast_sub hpq.le]
    exact_mod_cast hqmp
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hphiN : φ N ≤ C * (N : ℝ) ^ p := by
    calc
      φ N = ∑ i ∈ ({N} : Finset ℕ), φ i := by simp
      _ ≤ ∑ i ∈ Finset.Icc 0 N, φ i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_singleton] at hi
          subst i
          simp
        · intro i hi hnot
          exact hφ i
      _ ≤ C * (N : ℝ) ^ p := hpartial hN
  have htermN_eq :
      (N : ℝ) ^ p * ((N : ℝ)⁻¹ ^ q) =
        (N : ℝ) ^ (-((q - p : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast (N : ℝ) p,
      ← Real.rpow_natCast ((N : ℝ)⁻¹) q,
      Real.inv_rpow hNpos.le, ← Real.rpow_neg hNpos.le,
      ← Real.rpow_add hNpos]
    congr 1
    rw [Nat.cast_sub hpq.le]
    ring
  have htermN :
      φ N * ((N : ℝ)⁻¹ ^ q) ≤
        C * ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := by
    calc
      φ N * ((N : ℝ)⁻¹ ^ q) ≤
          (C * (N : ℝ) ^ p) * ((N : ℝ)⁻¹ ^ q) := by
            gcongr
      _ = C * ((N : ℝ) ^ p * ((N : ℝ)⁻¹ ^ q)) := by ring
      _ = C * ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := by rw [htermN_eq]
  refine Real.tsum_le_of_sum_le hnonneg ?_
  intro u
  let U : Finset ℕ := u.filter (fun n => N ≤ n)
  have hsum_filter :
      (∑ n ∈ u, if N ≤ n then φ n * ((n : ℝ)⁻¹ ^ q) else 0) =
        ∑ n ∈ U, φ n * ((n : ℝ)⁻¹ ^ q) := by
    simpa [U] using
      (Finset.sum_filter (s := u) (p := fun n => N ≤ n)
        (f := fun n => φ n * ((n : ℝ)⁻¹ ^ q))).symm
  by_cases hu : U.Nonempty
  ·
    have hU : U.Nonempty := by simpa [U] using hu
    let b : ℕ := U.max' hU
    have hbU : b ∈ U := by exact Finset.max'_mem U hU
    have hNb : N ≤ b := by
      exact (Finset.mem_filter.mp hbU).2
    have hUsub : U ⊆ Finset.Icc N b := by
      intro n hn
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_filter.mp hn).2, U.le_max' n hn⟩
    have hsumU :
        (∑ n ∈ U, φ n * ((n : ℝ)⁻¹ ^ q)) ≤
          ∑ n ∈ Finset.Icc N b, φ n * ((n : ℝ)⁻¹ ^ q) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hUsub
      intro n hn hnot
      exact mul_nonneg (hφ n) (by positivity)
    rw [hsum_filter]
    calc
      (∑ n ∈ U, φ n * ((n : ℝ)⁻¹ ^ q)) ≤
          ∑ n ∈ Finset.Icc N b, φ n * ((n : ℝ)⁻¹ ^ q) := hsumU
      _ = φ N * ((N : ℝ)⁻¹ ^ q) +
            ∑ n ∈ Finset.Ioc N b, φ n * ((n : ℝ)⁻¹ ^ q) := by
        exact (Finset.add_sum_Ioc_eq_sum_Icc hNb).symm
      _ ≤ C * ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) +
            C * (1 + (q : ℝ) / ((q : ℝ) - (p : ℝ))) *
              ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := by
        exact add_le_add htermN
          (sum_Ioc_inv_pow_tail_le_of_partial_sum hC hN hNb hpq hφ hpartial)
      _ = C * (2 + (q : ℝ) / ((q : ℝ) - (p : ℝ))) *
            ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := by
        ring
  · have hUempty : U = ∅ := (Finset.not_nonempty_iff_eq_empty).mp hu
    rw [hsum_filter, hUempty]
    simp
    positivity

/- A reindexing identity for a genuine disjoint partition.  It is the tsum
   counterpart of `summable_partition`; recording it explicitly avoids
   silently treating a partition as a finite sum. -/
theorem tsum_eq_tsum_partition
    {α β : Type*} {f : β → ℝ} (hf : Summable f) {s : α → Set β}
    (hs : ∀ i, ∃! j, i ∈ s j) :
    (∑' i : β, f i) = ∑' j, ∑' i : s j, f i := by
  let e : (j : α) × s j ≃ β := Set.sigmaEquiv s hs
  have hsig : Summable (f ∘ e) := e.summable_iff.mpr hf
  calc
    (∑' i : β, f i) = ∑' z : (j : α) × s j, f (e z) :=
      (e.tsum_eq f).symm
    _ = ∑' j : α, ∑' i : s j, f (e ⟨j, i⟩) := hsig.tsum_sigma
    _ = ∑' j : α, ∑' i : s j, f i := by
      apply tsum_congr
      intro j
      apply tsum_congr
      intro i
      rfl

/- [Lean infrastructure] The unit-height shells used in the paper's
   summation-by-parts argument.
   They retain the integer indexing of the count function while making the
   lower and upper height cutoffs explicit. -/
def heightShell {α : Type*} (H : α → ℝ) (n : ℕ) : Set α :=
  {x | (n : ℝ) ≤ H x ∧ H x < ((n + 1 : ℕ) : ℝ)}

/- [Lean infrastructure] The height interval occurring on the left side of
   the manuscript's first shell estimate (lines 640--647). -/
def heightInterval {α : Type*} (H : α → ℝ) (a b : ℕ) : Set α :=
  {x | (a : ℝ) ≤ H x ∧ H x < (b : ℝ)}

theorem heightShell_disjoint {α : Type*} {H : α → ℝ} {n₁ n₂ : ℕ}
    (hne : n₁ ≠ n₂) : Disjoint (heightShell H n₁) (heightShell H n₂) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hltR : (n₁ : ℝ) + 1 ≤ n₂ := by
      exact_mod_cast (Nat.succ_le_of_lt hlt)
    rw [Set.disjoint_left]
    intro x h₁ h₂
    have hupper : H x < (n₁ : ℝ) + 1 := by
      simpa [heightShell, Nat.cast_add_one] using h₁.2
    exact (not_le_of_gt hupper) (hltR.trans h₂.1)
  · have hgtR : (n₂ : ℝ) + 1 ≤ n₁ := by
      exact_mod_cast (Nat.succ_le_of_lt hgt)
    rw [Set.disjoint_left]
    intro x h₁ h₂
    have hupper : H x < (n₂ : ℝ) + 1 := by
      simpa [heightShell, Nat.cast_add_one] using h₂.2
    exact (not_le_of_gt hupper) (hgtR.trans h₁.1)

theorem heightShell_pairwiseDisjoint {α : Type*} {H : α → ℝ} :
    (Set.univ : Set {n : ℕ // 1 ≤ n}).PairwiseDisjoint
      (fun n => heightShell H n) := by
  intro n hn m hm hne
  apply heightShell_disjoint
  intro hnm
  exact hne (Subtype.ext hnm)

theorem mem_heightShell_unique {α : Type*} {H : α → ℝ} {x : α}
    {n₁ n₂ : ℕ} (h₁ : x ∈ heightShell H n₁)
    (h₂ : x ∈ heightShell H n₂) : n₁ = n₂ := by
  by_contra hne
  exact Set.disjoint_left.1 (heightShell_disjoint hne) h₁ h₂

theorem exists_mem_heightShell_of_one_le {α : Type*} {H : α → ℝ} {x : α}
    (hx : 1 ≤ H x) : ∃ n : ℕ, 1 ≤ n ∧ x ∈ heightShell H n := by
  let n : ℕ := ⌊H x⌋₊
  refine ⟨n, ?_, ?_⟩
  · exact Nat.one_le_floor_iff (H x) |>.2 hx
  · constructor
    · exact Nat.floor_le (by positivity)
    · simpa [n, Nat.cast_add_one] using (Nat.lt_floor_add_one (H x))

theorem iUnion_heightShell {α : Type*} {H : α → ℝ} :
    ⋃ n : {n : ℕ // 1 ≤ n}, heightShell H n = {x | 1 ≤ H x} := by
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    exact le_trans (by exact_mod_cast n.property) hn.1
  · intro hx
    obtain ⟨n, hn, hxn⟩ := exists_mem_heightShell_of_one_le hx
    exact Set.mem_iUnion.2 ⟨⟨n, hn⟩, hxn⟩

theorem heightShell_finite {α : Type*} {H : α → ℝ} {p : ℕ}
    (hcount : HasHeightCountBounds H p) {n : ℕ} (hn : 1 ≤ n) :
    (heightShell H n).Finite := by
  obtain ⟨cₗ, cᵤ, hcₗ, hcᵤ, hcut⟩ := hcount
  have hT : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ n + 1)
  apply (hcut ((n + 1 : ℕ) : ℝ) hT).1.subset
  intro x hx
  exact hx.2.le

/- [derived consequence, paper lines 640--647] A bounded height interval is
   finite under the height-count input. -/
theorem heightInterval_finite {α : Type*} {H : α → ℝ} {p a b : ℕ}
    (hcount : HasHeightCountBounds H p) (ha : 1 ≤ a) (hab : a ≤ b) :
    (heightInterval H a b).Finite := by
  obtain ⟨cₗ, cᵤ, hcₗ, hcᵤ, hcut⟩ := hcount
  have hb : 1 ≤ b := le_trans ha hab
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  apply (hcut (b : ℝ) hbR).1.subset
  intro x hx
  exact hx.2.le

/- [derived consequence, paper lines 640--647] This is the paper's first
   ordinary-shell comparison: each point in the height interval is assigned
   to its unit shell, and its reciprocal height is bounded by the reciprocal
   of the shell index.  The finite-set formulation makes the finiteness
   needed for the displayed sums explicit. -/
theorem finite_height_interval_sum_inv_pow_le_shell_sum
    {α : Type*} {H : α → ℝ} {p a b q : ℕ}
    (hcount : HasHeightCountBounds H p) (ha : 1 ≤ a) (hab : a ≤ b) :
    let hs := heightInterval_finite hcount ha hab
    (∑ x ∈ hs.toFinset, (H x)⁻¹ ^ q) ≤
      ∑ n ∈ Finset.Ico a b,
        (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) := by
  classical
  let hs := heightInterval_finite hcount ha hab
  have hfin_shell : ∀ n : ℕ, (heightShell H n).Finite := by
    intro n
    obtain ⟨cₗ, cᵤ, hcₗ, hcᵤ, hcut⟩ := hcount
    have hT : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ n + 1)
    apply (hcut ((n + 1 : ℕ) : ℝ) hT).1.subset
    intro x hx
    exact hx.2.le
  let I : Finset ℕ := Finset.Ico a b
  let F : ℕ → Finset α := fun n => (hfin_shell n).toFinset
  let U : Finset α := I.biUnion F
  have hdisj : (I : Set ℕ).PairwiseDisjoint F := by
    intro i hi j hj hne
    change Disjoint (F i) (F j)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    apply Set.disjoint_left.1 (heightShell_disjoint hne)
    · exact (hfin_shell i).mem_toFinset.mp hxi
    · exact (hfin_shell j).mem_toFinset.mp hxj
  have hU : (U : Set α) = heightInterval H a b := by
    ext x
    constructor
    · intro hx
      simp only [U, Finset.mem_coe, Finset.mem_biUnion] at hx
      obtain ⟨n, hn, hxn⟩ := hx
      have hxn' := (hfin_shell n).mem_toFinset.mp hxn
      have hnI := Finset.mem_Ico.mp hn
      constructor
      · exact le_trans (by exact_mod_cast hnI.1) hxn'.1
      · have hnstep : ((n + 1 : ℕ) : ℝ) ≤ (b : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hnI.2)
        exact lt_of_lt_of_le hxn'.2 hnstep
    · intro hx
      let n : ℕ := ⌊H x⌋₊
      have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (Nat.zero_le a)
      have hxnonneg : 0 ≤ H x := le_trans haR hx.1
      have hna : a ≤ n := by
        apply (Nat.le_floor_iff'
          (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one ha))).2
        exact hx.1
      have hnb : n < b := by
        apply (Nat.floor_lt'
          (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one
            (le_trans ha hab)))).2
        exact hx.2
      have hnI : n ∈ I := by
        exact Finset.mem_Ico.2 ⟨hna, hnb⟩
      have hxn : x ∈ heightShell H n := by
        constructor
        · exact Nat.floor_le hxnonneg
        · simpa [n, Nat.cast_add_one] using Nat.lt_floor_add_one (H x)
      exact Finset.mem_biUnion.2 ⟨n, hnI, (hfin_shell n).mem_toFinset.2 hxn⟩
  have hUfin : U = hs.toFinset := by
    apply Finset.ext
    intro x
    change x ∈ (U : Set α) ↔ x ∈ hs.toFinset
    rw [hs.mem_toFinset]
    exact Set.ext_iff.mp hU x
  have hsumU :
      (∑ x ∈ U, (H x)⁻¹ ^ q) =
        ∑ n ∈ I, ∑ x ∈ F n, (H x)⁻¹ ^ q := by
    simpa [U] using
      (Finset.sum_biUnion (s := I) (t := F) hdisj
        (f := fun x : α => (H x)⁻¹ ^ q))
  calc
    (∑ x ∈ hs.toFinset, (H x)⁻¹ ^ q) =
        ∑ x ∈ U, (H x)⁻¹ ^ q := by rw [hUfin]
    _ = ∑ n ∈ I, ∑ x ∈ F n, (H x)⁻¹ ^ q := hsumU
    _ ≤ ∑ n ∈ I,
        (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one
        (le_trans ha (Finset.mem_Ico.mp hn).1)
      have hpoint : ∀ x ∈ F n,
          (H x)⁻¹ ^ q ≤ (n : ℝ)⁻¹ ^ q := by
        intro x hx
        have hxn := (hfin_shell n).mem_toFinset.mp hx
        have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
        have hHR : 0 < H x := lt_of_lt_of_le hnR hxn.1
        have hinv : (H x)⁻¹ ≤ (n : ℝ)⁻¹ :=
          (inv_le_inv₀ hHR hnR).2 hxn.1
        exact pow_le_pow_left₀ (inv_nonneg.mpr hHR.le) hinv q
      have hsum :
          (∑ x ∈ F n, (H x)⁻¹ ^ q) ≤
            ∑ x ∈ F n, (n : ℝ)⁻¹ ^ q := by
        apply Finset.sum_le_sum
        intro x hx
        exact hpoint x hx
      have hcard : (Set.ncard (heightShell H n) : ℝ) = (F n).card := by
        dsimp [F]
        exact_mod_cast Set.ncard_eq_toFinset_card (heightShell H n) (hfin_shell n)
      rw [hcard]
      simpa using hsum


/- [derived consequence, paper lines 642--653] The cumulative cardinality of
   the ordinary shells is bounded by the height counting function. -/
theorem heightShell_partial_sum_upper {α : Type*} {H : α → ℝ} {p : ℕ}
    (hcount : HasHeightCountBounds H p) :
    ∃ cᵤ : ℝ, 0 < cᵤ ∧ ∀ {n : ℕ}, 1 ≤ n →
      (∑ i ∈ Finset.Ico 1 n,
        (Set.ncard (heightShell H i) : ℝ)) ≤ cᵤ * (n : ℝ) ^ p := by
  obtain ⟨cₗ, cᵤ, hcₗ, hcᵤ, hcut⟩ := hcount
  refine ⟨cᵤ, hcᵤ, ?_⟩
  intro n hn
  classical
  let I : Finset ℕ := Finset.Ico 1 n
  have hfin_shell : ∀ i : ℕ, (heightShell H i).Finite := by
    intro i
    have hT : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ i + 1)
    apply (hcut ((i + 1 : ℕ) : ℝ) hT).1.subset
    intro x hx
    exact hx.2.le
  let F : ℕ → Finset α := fun i => (hfin_shell i).toFinset
  let U : Finset α := I.biUnion F
  have hdisj : (I : Set ℕ).PairwiseDisjoint
      F := by
    intro i hi j hj hne
    change Disjoint (F i) (F j)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    apply Set.disjoint_left.1 (heightShell_disjoint hne)
    · exact (hfin_shell i).mem_toFinset.mp hxi
    · exact (hfin_shell j).mem_toFinset.mp hxj
  have hcardU : U.card = ∑ i ∈ I, (F i).card := by
    simpa [U] using (Finset.card_biUnion (s := I) hdisj)
  have hsum_card :
      (∑ i ∈ I, (Set.ncard (heightShell H i) : ℝ)) = (U.card : ℝ) := by
    calc
      (∑ i ∈ I, (Set.ncard (heightShell H i) : ℝ)) =
          ∑ i ∈ I, ((F i).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Set.ncard_eq_toFinset_card _ (hfin_shell i)]
      _ = (U.card : ℝ) := by
        exact_mod_cast hcardU.symm
  have hUsub : (U : Set α) ⊆ {x | H x ≤ (n : ℝ)} := by
    intro x hx
    simp only [U, Finset.mem_coe, Finset.mem_biUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    have hxi' := (hfin_shell i).mem_toFinset.mp hxi
    have hstep : ((i + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_Ico.mp hi).2)
    exact le_trans hxi'.2.le hstep
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hfinite : (Set.Finite {x | H x ≤ (n : ℝ)}) :=
    (hcut (n : ℝ) hnreal).1
  have hcardUle : U.card ≤ Set.ncard {x | H x ≤ (n : ℝ)} := by
    exact_mod_cast Set.ncard_le_ncard hUsub hfinite
  calc
    (∑ i ∈ Finset.Ico 1 n,
        (Set.ncard (heightShell H i) : ℝ)) = (U.card : ℝ) := by
          simpa [I] using hsum_card
    _ ≤ (Set.ncard {x | H x ≤ (n : ℝ)} : ℝ) := by exact_mod_cast hcardUle
    _ ≤ cᵤ * (n : ℝ) ^ p := (hcut (n : ℝ) hnreal).2.2

/- [derived consequence, paper lines 649--653] The Abel formula uses the
   cumulative shell count including the zero shell.  The zero shell is
   harmless but is recorded here explicitly rather than silently discarding
   it. -/
theorem heightShell_full_partial_sum_upper {α : Type*} {H : α → ℝ} {p : ℕ}
    (hcount : HasHeightCountBounds H p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ}, 1 ≤ n →
      (∑ i ∈ Finset.Icc 0 n,
        (Set.ncard (heightShell H i) : ℝ)) ≤ C * (n : ℝ) ^ p := by
  obtain ⟨c₀, hc₀, hpartial⟩ := heightShell_partial_sum_upper hcount
  obtain ⟨cₗ, cᵤ, hcₗ, hcᵤ, hcut⟩ := hcount
  refine ⟨cᵤ + c₀ * (2 : ℝ) ^ p, ?_, ?_⟩
  · positivity
  · intro n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hzero_finite : (Set.Finite {x | H x ≤ (1 : ℝ)}) :=
      (hcut 1 le_rfl).1
    have hzero_subset : heightShell H 0 ⊆ {x | H x ≤ (1 : ℝ)} := by
      intro x hx
      simpa [heightShell] using hx.2.le
    have hzero_card := Set.ncard_le_ncard hzero_subset hzero_finite
    have hzeroR : (Set.ncard (heightShell H 0) : ℝ) ≤ cᵤ := by
      have hzeroR' : (Set.ncard (heightShell H 0) : ℝ) ≤
          (Set.ncard {x | H x ≤ (1 : ℝ)} : ℝ) := by
        exact_mod_cast hzero_card
      exact hzeroR'.trans (by simpa using (hcut 1 le_rfl).2.2)
    have hsum_pos :
        (∑ i ∈ Finset.Icc 1 n,
          (Set.ncard (heightShell H i) : ℝ)) ≤
          c₀ * ((n + 1 : ℕ) : ℝ) ^ p := by
      simpa [Finset.Ico_add_one_right_eq_Icc, Nat.cast_add] using
        (hpartial (n := n + 1) (by omega))
    have hstep : (n + 1 : ℝ) ≤ 2 * n := by nlinarith
    have hpow : (n + 1 : ℝ) ^ p ≤ (2 * n) ^ p :=
      pow_le_pow_left₀ (by positivity) hstep p
    have hsum_pos' :
        (∑ i ∈ Finset.Icc 1 n,
          (Set.ncard (heightShell H i) : ℝ)) ≤
          c₀ * (2 * n) ^ p :=
      hsum_pos.trans (mul_le_mul_of_nonneg_left
        (by simpa [Nat.cast_add] using hpow) hc₀.le)
    have hIcc : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hsum_split :
        (∑ i ∈ Finset.Icc 0 n,
          (Set.ncard (heightShell H i) : ℝ)) =
          (Set.ncard (heightShell H 0) : ℝ) +
            ∑ i ∈ Finset.Icc 1 n,
              (Set.ncard (heightShell H i) : ℝ) := by
      rw [hIcc, Finset.sum_insert]
      simp
    have hnpow : (1 : ℝ) ≤ (n : ℝ) ^ p := one_le_pow₀ hnR
    rw [hsum_split]
    calc
      (Set.ncard (heightShell H 0) : ℝ) +
          ∑ i ∈ Finset.Icc 1 n,
            (Set.ncard (heightShell H i) : ℝ) ≤
          cᵤ + c₀ * (2 * n) ^ p :=
        add_le_add hzeroR hsum_pos'
      _ = cᵤ + c₀ * (2 : ℝ) ^ p * (n : ℝ) ^ p := by
        rw [mul_pow]
        ring
      _ ≤ cᵤ * (n : ℝ) ^ p +
          c₀ * (2 : ℝ) ^ p * (n : ℝ) ^ p := by
        gcongr
        simpa using (mul_le_mul_of_nonneg_left hnpow hcᵤ.le)
      _ = (cᵤ + c₀ * (2 : ℝ) ^ p) * (n : ℝ) ^ p := by ring

/- [derived consequence, paper lines 649--653 and corollary `co:tail`]
   Quantitative tail for the actual unit-height shell series.  This is the
   height-counting part of the manuscript's tail argument; the matrix weight
   and echelon normalization are intentionally not folded into this lemma. -/
set_option maxHeartbeats 1000000 in
theorem heightShell_tsum_indicator_Ici_inv_pow_le
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hpq : p < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ}, 1 ≤ N →
      (∑' n : ℕ, if N ≤ n then
        (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) else 0) ≤
        C * ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := by
  obtain ⟨C, hC, hpartial⟩ := heightShell_full_partial_sum_upper hcount
  let Ctail : ℝ := C * (2 + (q : ℝ) / ((q : ℝ) - (p : ℝ)))
  refine ⟨Ctail, ?_, ?_⟩
  · dsimp [Ctail]
    have hqmpR : (0 : ℝ) < (q : ℝ) - (p : ℝ) := by
      rw [← Nat.cast_sub hpq.le]
      exact_mod_cast (show 0 < q - p by omega)
    positivity
  · intro N hN
    dsimp [Ctail]
    apply tsum_indicator_Ici_inv_pow_le_of_partial_sum hC hN hpq
    · intro n
      positivity
    · intro n hn
      exact hpartial hn

/- [derived consequence, paper lines 649--653] Applying the quantitative Abel
   estimate to the height shells gives a height-count version ready for the
   tail arguments.  Its `Ioc` endpoint convention is the one used by the
   imported Abel identity; the preceding finite comparison handles the
   manuscript's `a ≤ H(x) < b` convention. -/
theorem heightShell_sum_Ioc_inv_pow_le
    {α : Type*} {H : α → ℝ} {p a b q : ℕ}
    (hcount : HasHeightCountBounds H p) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧
      (∑ n ∈ Finset.Ioc a b,
        (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) ≤
        C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) +
          C * (q : ℝ) *
            (∫ x in (a : ℝ)..(b : ℝ),
              x ^ p * (x⁻¹ ^ (q + 1))) := by
  obtain ⟨C, hC, hpartial⟩ := heightShell_full_partial_sum_upper hcount
  refine ⟨C, hC, ?_⟩
  apply sum_Ioc_inv_pow_le_of_partial_sum (φ := fun n =>
    (Set.ncard (heightShell H n) : ℝ)) ha hab hC.le
  · intro n
    positivity
  · intro n hn
    exact hpartial hn

/- [derived consequence, paper lines 649--653] A finite ordinary-shell sum
   therefore has the three sign-dependent sizes dictated by the exponent
   `p - q`: power growth, logarithmic growth, or a bounded contribution.  The
   last branch is deliberately bounded rather than assigned a negative power
   of the cutoff; this is the case distinction needed in the low-rank estimate
   before any application-specific normalization. -/
set_option maxHeartbeats 1000000 in
theorem heightShell_sum_Ioc_one_le_by_exponent
    {α : Type*} {H : α → ℝ} {p q b : ℕ}
    (hcount : HasHeightCountBounds H p) (hb : 1 ≤ b) :
    ∃ C : ℝ, 0 < C ∧
      (∑ n ∈ Finset.Ioc 1 b,
        (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) ≤
        if q < p then C * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
        else if p = q then C * (1 + Real.log (b : ℝ))
        else C := by
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < (b : ℝ) := lt_of_lt_of_le zero_lt_one hbR
  obtain ⟨C, hC, hmain⟩ := heightShell_sum_Ioc_inv_pow_le
    (H := H) (p := p) (a := 1) (b := b) (q := q) hcount le_rfl hb
  norm_num at hmain
  by_cases hqp : q < p
  · have hpq : p ≠ q := by omega
    have hqple : q ≤ p := hqp.le
    have hdiff_cast : (p : ℝ) - q = ((p - q : ℕ) : ℝ) := by
      rw [Nat.cast_sub hqple]
    have hdiff : 0 < (p : ℝ) - q := by
      rw [hdiff_cast]
      exact_mod_cast (show 0 < p - q by omega)
    have hendpoint_base :
        (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) =
          (b : ℝ) ^ ((p : ℝ) - q) := by
      rw [← Real.rpow_natCast (b : ℝ) p,
        ← Real.rpow_natCast ((b : ℝ)⁻¹) q,
        Real.inv_rpow hbpos.le, ← Real.rpow_neg hbpos.le,
        ← Real.rpow_add hbpos]
      congr 1
    have hendpoint :
        (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) =
          (b : ℝ) ^ ((p - q : ℕ) : ℝ) := by
      rw [hendpoint_base, hdiff_cast]
    have hIntegral := intervalIntegral_nat_power_inv_power
      (p := p) (q := q) (N := b) (by exact hb) hpq
    have hIntegralBound :
        (((b : ℝ) ^ ((p - q : ℕ) : ℝ) - 1) /
          ((p : ℝ) - q)) ≤
          (b : ℝ) ^ ((p - q : ℕ) : ℝ) /
            ((p : ℝ) - q) := by
      apply div_le_div_of_nonneg_right _ hdiff.le
      linarith
    refine ⟨C * (1 + (q : ℝ) / ((p : ℝ) - q)), by positivity, ?_⟩
    simp only [hqp, ↓reduceIte]
    calc
      (∑ n ∈ Finset.Ioc 1 b,
          (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) ≤
          C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) +
            C * (q : ℝ) *
              (∫ x in (1 : ℝ)..(b : ℝ),
                x ^ p * (x⁻¹ ^ (q + 1))) := by
        simpa only [inv_pow] using hmain
      _ = C * (b : ℝ) ^ ((p - q : ℕ) : ℝ) +
            C * (q : ℝ) *
              (((b : ℝ) ^ ((p - q : ℕ) : ℝ) - 1) /
                ((p : ℝ) - q)) := by
          rw [show C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) =
            C * ((b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q)) by ring,
            hendpoint, hIntegral, hdiff_cast]
      _ ≤ C * (b : ℝ) ^ ((p - q : ℕ) : ℝ) +
            C * (q : ℝ) *
              ((b : ℝ) ^ ((p - q : ℕ) : ℝ) /
                ((p : ℝ) - q)) := by
        gcongr
      _ = C * (1 + (q : ℝ) / ((p : ℝ) - q)) *
            (b : ℝ) ^ ((p - q : ℕ) : ℝ) := by ring
  · by_cases hpq : p = q
    · subst q
      have hIntegral := intervalIntegral_nat_power_inv_power_eq_log
        (p := p) (N := b) hb
      have hendpoint :
          (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ p) = 1 := by
        rw [← Real.rpow_natCast (b : ℝ) p,
          ← Real.rpow_natCast ((b : ℝ)⁻¹) p,
          Real.inv_rpow hbpos.le, ← Real.rpow_neg hbpos.le,
          ← Real.rpow_add hbpos]
        rw [show (p : ℝ) + -(p : ℝ) = 0 by ring, Real.rpow_zero]
      have hendpoint_C :
          C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ p) = C := by
        calc
          C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ p) =
              C * ((b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ p)) := by ring
          _ = C := by rw [hendpoint]; ring
      have hlog : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hbR
      refine ⟨C * (1 + (p : ℝ)), by positivity, ?_⟩
      simp only [lt_irrefl, ↓reduceIte]
      calc
        (∑ n ∈ Finset.Ioc 1 b,
            (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ p)) ≤
            C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ p) +
              C * (p : ℝ) *
                (∫ x in (1 : ℝ)..(b : ℝ),
                x ^ p * (x⁻¹ ^ (p + 1))) := by
          simpa only [inv_pow] using hmain
      _ = C + C * (p : ℝ) * Real.log (b : ℝ) := by
          rw [hendpoint_C, hIntegral]
      _ ≤ C * (1 + (p : ℝ)) * (1 + Real.log (b : ℝ)) := by
        have hnonneg : 0 ≤ C * ((p : ℝ) + Real.log (b : ℝ)) :=
          mul_nonneg hC.le (add_nonneg (by positivity) hlog)
        nlinarith
    · have hpq' : p < q := by omega
      have hdiff_cast : (q : ℝ) - p = ((q - p : ℕ) : ℝ) := by
        rw [Nat.cast_sub hpq'.le]
      have hdiff : 0 < (q : ℝ) - p := by
        rw [hdiff_cast]
        exact_mod_cast (show 0 < q - p by omega)
      have hendpoint_base :
          (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) =
            (b : ℝ) ^ ((p : ℝ) - q) := by
        rw [← Real.rpow_natCast (b : ℝ) p,
          ← Real.rpow_natCast ((b : ℝ)⁻¹) q,
          Real.inv_rpow hbpos.le, ← Real.rpow_neg hbpos.le,
          ← Real.rpow_add hbpos]
        congr 1
      have hnegdiff_cast : (p : ℝ) - q = -((q - p : ℕ) : ℝ) := by
        rw [Nat.cast_sub hpq'.le]
        ring
      have hendpoint :
          (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) =
            (b : ℝ) ^ (-((q - p : ℕ) : ℝ)) := by
        rw [hendpoint_base, hnegdiff_cast]
      have hIntegral := intervalIntegral_nat_power_inv_power
        (p := p) (q := q) (N := b) (by exact hb) (by omega)
      have hIntegralBound :
          (((b : ℝ) ^ (-((q - p : ℕ) : ℝ)) - 1) /
            ((p : ℝ) - q)) ≤
            1 / ((q : ℝ) - p) := by
        have hdenom : (p : ℝ) - q = -((q - p : ℕ) : ℝ) := hnegdiff_cast
        rw [hdenom]
        calc
          ((b : ℝ) ^ (-((q - p : ℕ) : ℝ)) - 1) /
              (-((q - p : ℕ) : ℝ)) =
              (1 - (b : ℝ) ^ (-((q - p : ℕ) : ℝ))) /
                ((q - p : ℕ) : ℝ) := by ring
          _ ≤ 1 / ((q - p : ℕ) : ℝ) := by
            apply div_le_div_of_nonneg_right _ (le_of_lt (by exact_mod_cast
              (show 0 < q - p by omega)))
            exact sub_le_self 1
              (Real.rpow_nonneg (le_trans (by norm_num) hbR) _)
          _ = 1 / ((q : ℝ) - p) := by
            rw [hdiff_cast]
      refine ⟨C * (1 + (q : ℝ) / ((q : ℝ) - p)), by positivity, ?_⟩
      simp only [hqp, hpq, ↓reduceIte]
      calc
        (∑ n ∈ Finset.Ioc 1 b,
            (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) ≤
            C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) +
              C * (q : ℝ) *
                (∫ x in (1 : ℝ)..(b : ℝ),
                x ^ p * (x⁻¹ ^ (q + 1))) := by
          simpa only [inv_pow] using hmain
      _ ≤ C * 1 + C * (q : ℝ) * (1 / ((q : ℝ) - p)) := by
          rw [show C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) =
            C * ((b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q)) by ring,
            hendpoint, hIntegral, hnegdiff_cast]
          have hbpow_le :
              (b : ℝ) ^ (-((q - p : ℕ) : ℝ)) ≤ 1 := by
            have hnegexp : -((q - p : ℕ) : ℝ) ≤ 0 := by
              have hdiff_nat : 0 < ((q - p : ℕ) : ℝ) := by
                exact_mod_cast (show 0 < q - p by omega)
              linarith
            have hpow := Real.rpow_le_rpow_of_exponent_le hbR hnegexp
            simpa using hpow
          have hfirst : (C : ℝ) * (b : ℝ) ^ (-((q - p : ℕ) : ℝ)) ≤ C * 1 := by
            simpa using mul_le_mul_of_nonneg_left hbpow_le hC.le
          have hIntegralBound' :
              (((b : ℝ) ^ (-((q - p : ℕ) : ℝ)) - 1) /
                (-((q - p : ℕ) : ℝ))) ≤
              1 / ((q : ℝ) - p) := by
            simpa [hnegdiff_cast] using hIntegralBound
          have hsecond : C * (q : ℝ) *
              (((b : ℝ) ^ (-((q - p : ℕ) : ℝ)) - 1) /
                (-((q - p : ℕ) : ℝ))) ≤
              C * (q : ℝ) * (1 / ((q : ℝ) - p)) := by
            exact mul_le_mul_of_nonneg_left hIntegralBound'
              (mul_nonneg hC.le (by positivity))
          exact add_le_add hfirst hsecond
        _ = C * (1 + (q : ℝ) / ((q : ℝ) - p)) := by ring

/- [derived consequence, paper lines 642--653] Abel summation upgrades the
   shellwise estimate to the sharp threshold `p < q`.  The imported Mathlib
   lemma used here is itself the finite/infinite Abel argument; the ordinary
   unit-shell indexing remains the one displayed in the manuscript. -/
theorem summable_heightShell_inv_pow_of_lt
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hpq : p < q) :
    Summable (fun n : ℕ =>
      (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) := by
  obtain ⟨cᵤ, hcᵤ, hpartial⟩ := heightShell_partial_sum_upper hcount
  let c : ℕ → ℂ := fun n => (Set.ncard (heightShell H n) : ℂ)
  have hO : (fun n : ℕ =>
      ∑ k ∈ Finset.Icc 1 n, ‖c k‖) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ p) := by
    refine Asymptotics.IsBigO.of_bound (cᵤ * (2 : ℝ) ^ p) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsum := hpartial (n := n + 1) (by omega)
    have hstep : (n + 1 : ℝ) ≤ 2 * n := by nlinarith
    have hpow : (n + 1 : ℝ) ^ p ≤ (2 * n) ^ p :=
      pow_le_pow_left₀ (by positivity) hstep p
    have hsum' : (∑ k ∈ Finset.Icc 1 n,
        (Set.ncard (heightShell H k) : ℝ)) ≤ cᵤ * (n + 1 : ℝ) ^ p := by
      simpa [Finset.Ico_add_one_right_eq_Icc, Nat.cast_add] using hsum
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k hk => norm_nonneg (c k))]
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ p)]
    calc
      (∑ k ∈ Finset.Icc 1 n, ‖c k‖) =
          ∑ k ∈ Finset.Icc 1 n,
          (Set.ncard (heightShell H k) : ℝ) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp [c]
      _ ≤ cᵤ * (n + 1 : ℝ) ^ p := hsum'
      _ ≤ cᵤ * (2 * n) ^ p := by
        exact mul_le_mul_of_nonneg_left hpow hcᵤ.le
      _ = (cᵤ * (2 : ℝ) ^ p) * (n : ℝ) ^ p := by ring
  have hO' : (fun n : ℕ =>
      ∑ k ∈ Finset.Icc 1 n, ‖c k‖) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (p : ℝ)) := by
    simpa only [Real.rpow_natCast] using hO
  have hL : LSeriesSummable c (q : ℂ) := by
    apply LSeriesSummable_of_sum_norm_bigO (r := (p : ℝ)) hO'
    · positivity
    · exact_mod_cast hpq
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term c (q : ℂ) n‖) := by
    exact (show Summable (LSeries.term c (q : ℂ)) from hL).norm
  apply hnorm.congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · have hq : 0 < q := by omega
    simp [LSeries.term_zero, hq.ne']
  · rw [LSeries.norm_term_eq]
    simp only [hn, ite_false, c, Complex.norm_natCast]
    change (Set.ncard (heightShell H n) : ℝ) /
      (n : ℝ) ^ (q : ℝ) =
      (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)
    rw [Real.rpow_natCast, div_eq_mul_inv, ← inv_pow]

theorem heightShell_ncard_upper {α : Type*} {H : α → ℝ} {p : ℕ}
    (hcount : HasHeightCountBounds H p) :
    ∃ cᵤ : ℝ, 0 < cᵤ ∧ ∀ {n : ℕ}, 1 ≤ n →
      (Set.ncard (heightShell H n) : ℝ) ≤
        cᵤ * ((n + 1 : ℕ) : ℝ) ^ p := by
  obtain ⟨cₗ, cᵤ, hcₗ, hcᵤ, hcut⟩ := hcount
  refine ⟨cᵤ, hcᵤ, ?_⟩
  intro n hn
  have hT : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ n + 1)
  have hfinite :
      (Set.Finite {x | H x ≤ ((n + 1 : ℕ) : ℝ)}) :=
    (hcut ((n + 1 : ℕ) : ℝ) hT).1
  have hsubset : heightShell H n ⊆
      {x | H x ≤ ((n + 1 : ℕ) : ℝ)} := by
    intro x hx
    exact hx.2.le
  have hcard := Set.ncard_le_ncard hsubset hfinite
  have hupper := (hcut ((n + 1 : ℕ) : ℝ) hT).2.2
  have hcardR : (Set.ncard (heightShell H n) : ℝ) ≤
      (Set.ncard {x | H x ≤ ((n + 1 : ℕ) : ℝ)} : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans hupper

/- The manuscript sums over all positive-height subspaces below a cutoff.  The
   Abel lemma above uses `Ioc 1 b`, which omits the first shell; this wrapper
   restores that shell before the three-case estimate is used in the
   low-rank argument. -/
set_option maxHeartbeats 1000000 in
theorem heightShell_sum_Icc_one_le_by_exponent
    {α : Type*} {H : α → ℝ} {p q b : ℕ}
    (hcount : HasHeightCountBounds H p) (hb : 1 ≤ b) :
    ∃ C : ℝ, 0 < C ∧
      (∑ n ∈ Finset.Icc 1 b,
        (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) ≤
        if q < p then C * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
        else if p = q then C * (1 + Real.log (b : ℝ))
        else C := by
  obtain ⟨C₀, hC₀, hIoc⟩ :=
    heightShell_sum_Ioc_one_le_by_exponent hcount hb
  obtain ⟨C₁, hC₁, hshell⟩ := heightShell_ncard_upper hcount
  have hshell₁ : (Set.ncard (heightShell H 1) : ℝ) ≤ C₁ * (2 : ℝ) ^ p := by
    simpa using (hshell (n := 1) (by omega : 1 ≤ (1 : ℕ)))
  have hsplit : Finset.Icc 1 b = insert 1 (Finset.Ioc 1 b) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hsum :
      (∑ n ∈ Finset.Icc 1 b,
        (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) =
      (Set.ncard (heightShell H 1) : ℝ) +
        ∑ n ∈ Finset.Ioc 1 b,
          (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) := by
    rw [hsplit, Finset.sum_insert]
    · simp
    · simp
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hlog : 1 ≤ 1 + Real.log (b : ℝ) := by
    linarith [Real.log_nonneg hbR]
  by_cases hqp : q < p
  · have hpow : (1 : ℝ) ≤ (b : ℝ) ^ ((p - q : ℕ) : ℝ) := by
      have hdiff_nonneg : (0 : ℝ) ≤ ((p - q : ℕ) : ℝ) := by positivity
      simpa using Real.rpow_le_rpow_of_exponent_le hbR hdiff_nonneg
    refine ⟨C₀ + C₁ * (2 : ℝ) ^ p, by positivity, ?_⟩
    simp only [hqp, ↓reduceIte]
    have hIoc' :
        (∑ n ∈ Finset.Ioc 1 b,
          (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) ≤
          C₀ * (b : ℝ) ^ ((p - q : ℕ) : ℝ) := by
      simpa only [hqp, ↓reduceIte] using hIoc
    calc
      (∑ n ∈ Finset.Icc 1 b,
          (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) =
          (Set.ncard (heightShell H 1) : ℝ) +
            ∑ n ∈ Finset.Ioc 1 b,
              (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) := hsum
      _ ≤ C₁ * (2 : ℝ) ^ p +
          C₀ * (b : ℝ) ^ ((p - q : ℕ) : ℝ) :=
        add_le_add hshell₁ hIoc'
      _ ≤ (C₀ + C₁ * (2 : ℝ) ^ p) *
          (b : ℝ) ^ ((p - q : ℕ) : ℝ) := by
        have hC₁pow : C₁ * (2 : ℝ) ^ p ≤
            (C₁ * (2 : ℝ) ^ p) *
              (b : ℝ) ^ ((p - q : ℕ) : ℝ) := by
          calc
            C₁ * (2 : ℝ) ^ p =
                (C₁ * (2 : ℝ) ^ p) * 1 := by ring
            _ ≤ (C₁ * (2 : ℝ) ^ p) *
                (b : ℝ) ^ ((p - q : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
        calc
          C₁ * (2 : ℝ) ^ p +
              C₀ * (b : ℝ) ^ ((p - q : ℕ) : ℝ) ≤
              (C₁ * (2 : ℝ) ^ p) *
                (b : ℝ) ^ ((p - q : ℕ) : ℝ) +
                C₀ * (b : ℝ) ^ ((p - q : ℕ) : ℝ) :=
            add_le_add hC₁pow le_rfl
          _ = (C₀ + C₁ * (2 : ℝ) ^ p) *
              (b : ℝ) ^ ((p - q : ℕ) : ℝ) := by ring
  · by_cases hpq : p = q
    · subst q
      refine ⟨C₀ + C₁ * (2 : ℝ) ^ p, by positivity, ?_⟩
      simp only [lt_irrefl, ↓reduceIte]
      have hIoc' :
          (∑ n ∈ Finset.Ioc 1 b,
            (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ p)) ≤
            C₀ * (1 + Real.log (b : ℝ)) := by
        simpa only [lt_irrefl, ↓reduceIte] using hIoc
      calc
        (∑ n ∈ Finset.Icc 1 b,
            (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ p)) =
            (Set.ncard (heightShell H 1) : ℝ) +
              ∑ n ∈ Finset.Ioc 1 b,
                (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ p) := hsum
        _ ≤ C₁ * (2 : ℝ) ^ p + C₀ * (1 + Real.log (b : ℝ)) := by
          exact add_le_add hshell₁ hIoc'
        _ ≤ (C₀ + C₁ * (2 : ℝ) ^ p) *
            (1 + Real.log (b : ℝ)) := by
          have hC₁pow : 0 ≤ C₁ * (2 : ℝ) ^ p := by positivity
          nlinarith [hlog]
    · have hpq' : p < q := by omega
      refine ⟨C₀ + C₁ * (2 : ℝ) ^ p, by positivity, ?_⟩
      simp only [hqp, hpq, ↓reduceIte]
      have hIoc' :
          (∑ n ∈ Finset.Ioc 1 b,
            (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) ≤ C₀ := by
        simpa only [hqp, hpq, ↓reduceIte] using hIoc
      calc
        (∑ n ∈ Finset.Icc 1 b,
            (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) =
            (Set.ncard (heightShell H 1) : ℝ) +
              ∑ n ∈ Finset.Ioc 1 b,
                (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) := hsum
        _ ≤ C₁ * (2 : ℝ) ^ p + C₀ := by
          exact add_le_add hshell₁ hIoc'
        _ = C₀ + C₁ * (2 : ℝ) ^ p := by ring

theorem heightShell_inv_pow_le {α : Type*} {H : α → ℝ}
    {n q : ℕ} (hn : 0 < n) {x : α} (hx : x ∈ heightShell H n) :
    (H x)⁻¹ ^ q ≤ (n : ℝ)⁻¹ ^ q := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hHR : 0 < H x := lt_of_lt_of_le hnR hx.1
  have hinv : (H x)⁻¹ ≤ (n : ℝ)⁻¹ :=
    (inv_le_inv₀ hHR hnR).2 hx.1
  exact pow_le_pow_left₀ (inv_nonneg.mpr hHR.le) hinv q

/- Finite-shell form of the preceding pointwise estimate.  This is the
   summand bound used when a height sum is grouped by integer shells. -/
theorem heightShell_sum_inv_pow_le
    {α : Type*} {H : α → ℝ} {p n q : ℕ}
    (hcount : HasHeightCountBounds H p) (hn : 0 < n) :
    let hs := heightShell_finite hcount (by exact hn)
    (∑ x ∈ hs.toFinset, (H x)⁻¹ ^ q) ≤
      (Set.ncard (heightShell H n) : ℝ) * (n : ℝ)⁻¹ ^ q := by
  let hs := heightShell_finite hcount (by exact hn)
  letI : Fintype (heightShell H n) := hs.fintype
  have hsum : (∑ x ∈ hs.toFinset, (H x)⁻¹ ^ q) ≤
      ∑ x ∈ hs.toFinset, (n : ℝ)⁻¹ ^ q := by
    apply Finset.sum_le_sum
    intro x hx
    apply heightShell_inv_pow_le hn
    exact hs.mem_toFinset.mp hx
  have hcard : (Set.ncard (heightShell H n) : ℝ) =
      (hs.toFinset.card : ℝ) := by
    rw [Set.ncard_eq_toFinset_card (heightShell H n) hs]
  rw [hcard]
  simpa using hsum

/- A finite family supported on positive heights below an integer cutoff is
   bounded by the corresponding complete shell sum.  This is the bridge from
   the paper's finite family `𝓕_l(T)` to the height-counting estimate. -/
set_option maxHeartbeats 1000000 in
theorem finite_height_inv_pow_sum_le_by_exponent
    {α : Type*} {H : α → ℝ} {p q b : ℕ}
    (hcount : HasHeightCountBounds H p) (hb : 1 ≤ b)
    (S : Set α) (hS : S.Finite)
    (hS_one : ∀ x ∈ S, 1 ≤ H x)
    (hS_bound : ∀ x ∈ S, H x ≤ (b : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      (∑ x ∈ hS.toFinset, (H x)⁻¹ ^ q) ≤
        if q < p then C * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
        else if p = q then C * (1 + Real.log (b : ℝ))
        else C := by
  let I : Finset ℕ := Finset.Icc 1 b
  have hShellFin (n : ℕ) (hn : n ∈ I) :
      (heightShell H n).Finite := by
    apply heightShell_finite hcount
    exact Finset.mem_Icc.mp hn |>.1
  have hFfin (n : ℕ) : (S ∩ heightShell H n).Finite := by
    apply hS.subset
    intro x hx
    exact hx.1
  let F : ℕ → Finset α := fun n => (hFfin n).toFinset
  let U : Finset α := I.biUnion F
  have hdisj : (I : Set ℕ).PairwiseDisjoint F := by
    intro i hi j hj hne
    change Disjoint (F i) (F j)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    apply Set.disjoint_left.1 (heightShell_disjoint hne)
    · exact (hFfin i).mem_toFinset.mp hxi |>.2
    · exact (hFfin j).mem_toFinset.mp hxj |>.2
  have hU : (U : Set α) = S := by
    ext x
    constructor
    · intro hx
      simp only [U, Finset.mem_coe, Finset.mem_biUnion] at hx
      obtain ⟨n, hn, hxn⟩ := hx
      exact (hFfin n).mem_toFinset.mp hxn |>.1
    · intro hx
      obtain ⟨n, hn, hxn⟩ := exists_mem_heightShell_of_one_le (hS_one x hx)
      have hnb : n ≤ b := by
        have hnr : (n : ℝ) ≤ (b : ℝ) :=
          le_trans hxn.1 (hS_bound x hx)
        exact_mod_cast hnr
      have hnI : n ∈ I := by
        exact Finset.mem_Icc.2 ⟨hn, hnb⟩
      exact Finset.mem_biUnion.2 ⟨n, hnI,
        (hFfin n).mem_toFinset.2 ⟨hx, hxn⟩⟩
  have hUfin : U = hS.toFinset := by
    apply Finset.ext
    intro x
    change x ∈ (U : Set α) ↔ x ∈ hS.toFinset
    rw [hU, hS.mem_toFinset]
  have hsumU :
      (∑ x ∈ U, (H x)⁻¹ ^ q) =
        ∑ n ∈ I, ∑ x ∈ F n, (H x)⁻¹ ^ q := by
    simpa [U] using
      (Finset.sum_biUnion (s := I) (t := F) hdisj
        (f := fun x : α => (H x)⁻¹ ^ q))
  have hFsum (n : ℕ) (hn : n ∈ I) :
      (∑ x ∈ F n, (H x)⁻¹ ^ q) ≤
        (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) := by
    have hnpos : 0 < n := lt_of_lt_of_le (by omega) (Finset.mem_Icc.mp hn).1
    have hfull := heightShell_sum_inv_pow_le (q := q) hcount hnpos
    have hsubset : F n ⊆ (hShellFin n hn).toFinset := by
      intro x hx
      exact (hShellFin n hn).mem_toFinset.2
        ((hFfin n).mem_toFinset.mp hx |>.2)
    have hnonneg : ∀ x ∈ (hShellFin n hn).toFinset,
        x ∉ F n → 0 ≤ (H x)⁻¹ ^ q := by
      intro x hx hnot
      have hxn := (hShellFin n hn).mem_toFinset.mp hx
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hHR : 0 < H x := lt_of_lt_of_le hnR hxn.1
      exact pow_nonneg (inv_nonneg.mpr hHR.le) q
    calc
      (∑ x ∈ F n, (H x)⁻¹ ^ q) ≤
          ∑ x ∈ (hShellFin n hn).toFinset, (H x)⁻¹ ^ q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
      _ ≤ (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) := by
        simpa using hfull
  obtain ⟨C, hC, hshell⟩ := heightShell_sum_Icc_one_le_by_exponent hcount hb
  refine ⟨C, hC, ?_⟩
  calc
    (∑ x ∈ hS.toFinset, (H x)⁻¹ ^ q) = ∑ x ∈ U, (H x)⁻¹ ^ q := by
      rw [hUfin]
    _ = ∑ n ∈ I, ∑ x ∈ F n, (H x)⁻¹ ^ q := hsumU
    _ ≤ ∑ n ∈ I,
        (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) := by
      exact Finset.sum_le_sum (fun n hn => hFsum n hn)
    _ ≤ if q < p then C * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
        else if p = q then C * (1 + Real.log (b : ℝ))
        else C := by
      simpa [I] using hshell

/- The weighted form used in the low-rank argument.  The support is kept as an
   explicit finite set: this is the formal counterpart of restricting to
   `𝓕_l(T)`, and it avoids replacing the manuscript's family by an unproved
   dyadic decomposition. -/
set_option maxHeartbeats 1000000 in
theorem tsum_abs_le_finite_height_inv_pow
    {α : Type*} {H : α → ℝ} {p q b : ℕ}
    (hcount : HasHeightCountBounds H p) (hb : 1 ≤ b)
    (w : α → ℝ) (S : Set α) (hS : S.Finite)
    (hS_one : ∀ x ∈ S, 1 ≤ H x)
    (hS_bound : ∀ x ∈ S, H x ≤ (b : ℝ))
    (hzero : ∀ x ∉ S, w x = 0) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ x ∈ S, |w x| ≤ C * (H x)⁻¹ ^ q) :
    ∃ D : ℝ, 0 < D ∧
      |∑' x : α, w x| ≤
        if q < p then C * D * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
        else if p = q then C * D * (1 + Real.log (b : ℝ))
        else C * D := by
  have hzero' : ∀ x ∉ hS.toFinset, w x = 0 := by
    intro x hx
    apply hzero
    exact fun hxs => hx (hS.mem_toFinset.2 hxs)
  have hsum : (∑' x : α, w x) = ∑ x ∈ hS.toFinset, w x :=
    tsum_eq_sum hzero'
  have hsumabs :
      |∑ x ∈ hS.toFinset, w x| ≤ ∑ x ∈ hS.toFinset, |w x| := by
    simpa [Real.norm_eq_abs] using
      (norm_sum_le (s := hS.toFinset) (f := w))
  have hpoint_sum :
      (∑ x ∈ hS.toFinset, |w x|) ≤
        ∑ x ∈ hS.toFinset, C * (H x)⁻¹ ^ q := by
    exact Finset.sum_le_sum (fun x hx => hw x (hS.mem_toFinset.1 hx))
  have hsum_scaled :
      (∑ x ∈ hS.toFinset, C * (H x)⁻¹ ^ q) =
        C * ∑ x ∈ hS.toFinset, (H x)⁻¹ ^ q := by
    rw [Finset.mul_sum]
  obtain ⟨D, hD, hheight⟩ :=
    finite_height_inv_pow_sum_le_by_exponent hcount hb S hS hS_one hS_bound
  have hCheight :
      C * (∑ x ∈ hS.toFinset, (H x)⁻¹ ^ q) ≤
        C * (if q < p then D * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
          else if p = q then D * (1 + Real.log (b : ℝ))
          else D) :=
    mul_le_mul_of_nonneg_left hheight hC
  refine ⟨D, hD, ?_⟩
  rw [hsum]
  calc
    |∑ x ∈ hS.toFinset, w x| ≤ ∑ x ∈ hS.toFinset, |w x| := hsumabs
    _ ≤ ∑ x ∈ hS.toFinset, C * (H x)⁻¹ ^ q := hpoint_sum
    _ = C * ∑ x ∈ hS.toFinset, (H x)⁻¹ ^ q := hsum_scaled
    _ ≤ C * (if q < p then D * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
        else if p = q then D * (1 + Real.log (b : ℝ))
        else D) := hCheight
    _ = if q < p then C * D * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
        else if p = q then C * D * (1 + Real.log (b : ℝ))
        else C * D := by
      by_cases hqp : q < p
      · simp only [hqp, ↓reduceIte]
        ring
      · by_cases hpq : p = q
        · simp only [hqp, hpq, lt_irrefl, ↓reduceIte]
          ring
        · simp only [hqp, hpq, ↓reduceIte]
 

/- The shell partition can be assembled into the actual reciprocal-height sum.
   The sharp `p < q` range comes from the Abel argument above.  We restrict to
   the positive-height part because reciprocal powers are used only for
   `H ≥ 1` in the manuscript's tail argument. -/
theorem summable_height_inv_pow_of_one_le
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hpq : p < q) :
    Summable (fun x : {x : α // 1 ≤ H x} => (H x.1)⁻¹ ^ q) := by
  let β := {x : α // 1 ≤ H x}
  let f : β → ℝ := fun x => (H x.1)⁻¹ ^ q
  let s : {n : ℕ // 1 ≤ n} → Set β :=
    fun n => {x | (x.1 : α) ∈ heightShell H n}
  have hs_unique : ∀ i : β, ∃! j : {n : ℕ // 1 ≤ n}, i ∈ s j := by
    intro i
    obtain ⟨n, hn, hin⟩ := exists_mem_heightShell_of_one_le i.2
    refine ⟨⟨n, hn⟩, hin, ?_⟩
    intro j hj
    apply Subtype.ext
    change (i : α) ∈ heightShell H j at hj
    exact mem_heightShell_unique hj hin
  have hs_finite : ∀ j, (s j).Finite := by
    intro j
    have hpre : ({x : β | (x : α) ∈ heightShell H j}).Finite := by
      apply (heightShell_finite hcount j.property).preimage
      intro x hx y hy hxy
      exact Subtype.ext hxy
    simpa [s] using hpre
  have hf_nonneg : ∀ i : β, 0 ≤ f i := by
    intro i
    apply pow_nonneg
    exact inv_nonneg.mpr (le_trans zero_le_one i.2)
  rw [summable_partition hf_nonneg hs_unique]
  constructor
  · intro j
    exact (hs_finite j).summable (fun i : β => f i)
  · let a : ℕ → ℝ := fun n =>
      (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)
    have ha : Summable a := by
      simpa [a] using (summable_heightShell_inv_pow_of_lt hcount hpq)
    have ha_sub : Summable (fun j : {n : ℕ // 1 ≤ n} => a j) := by
      simpa [Function.comp_def] using ha.subtype (fun n : ℕ => 1 ≤ n)
    let g : {n : ℕ // 1 ≤ n} → ℝ := fun j => ∑' i : s j, f i
    change Summable g
    refine Summable.of_nonneg_of_le
      (f := fun j : {n : ℕ // 1 ≤ n} => a j) (g := g)
      (fun j => tsum_nonneg (fun i => hf_nonneg i))
      (fun j => ?_)
      ha_sub
    let hs := hs_finite j
    letI : Fintype (s j) := hs.fintype
    have hcard : Fintype.card (s j) =
        Set.ncard (heightShell H j) := by
      have himage : ((fun x : β => (x : α)) '' s j) = heightShell H j := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          have hxone : 1 ≤ H x :=
            le_trans (by exact_mod_cast j.property) hx.1
          refine ⟨⟨x, hxone⟩, hx, rfl⟩
      have himcard : ((fun x : β => (x : α)) '' s j).ncard =
          (s j).ncard := by
        apply (Set.ncard_image_iff hs).2
        intro x hx y hy hxy
        exact Subtype.ext hxy
      calc
        Fintype.card (s j) = (s j).ncard := Set.fintypeCard_eq_ncard (s j)
        _ = ((fun x : β => (x : α)) '' s j).ncard := himcard.symm
        _ = Set.ncard (heightShell H j) := by rw [himage]
    have hinner : g j ≤ a j := by
      change (∑' i : s j, f i) ≤ a j
      rw [tsum_eq_sum (s := Finset.univ) (fun b hb =>
        (hb (Finset.mem_univ b)).elim)]
      calc
        (∑ x : s j, f x) ≤
            ∑ x : s j, ((j : ℝ)⁻¹ ^ q) := by
          apply Finset.sum_le_sum
          intro x hx
          have hjpos : 0 < (j : ℕ) :=
            lt_of_lt_of_le Nat.zero_lt_one j.property
          exact heightShell_inv_pow_le hjpos x.property
        _ = (Set.ncard (heightShell H j) : ℝ) * ((j : ℝ)⁻¹ ^ q) := by
          simp [Finset.sum_const, hcard]
        _ = a j := rfl
    exact hinner

/- [derived consequence, paper lines 837--858 and corollary `co:tail`]
   Quantitative reciprocal-height tail for points themselves.  The height
   count supplies the ordinary-shell bound; the remaining argument is only
   the proved partition of the positive-height stratum into unit shells. -/
set_option maxHeartbeats 1200000 in
theorem height_tsum_tail_inv_pow_le
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hpq : p < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ}, 1 ≤ N →
      (∑' x : {x : α // (N : ℝ) ≤ H x}, (H x.1)⁻¹ ^ q) ≤
        C * ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := by
  obtain ⟨C, hC, htail⟩ := heightShell_tsum_indicator_Ici_inv_pow_le
    hcount hpq
  refine ⟨C, hC, ?_⟩
  intro N hN
  let β := {x : α // 1 ≤ H x}
  let βN := {x : α // (N : ℝ) ≤ H x}
  let γ := {j : ℕ | N ≤ j}
  let f : βN → ℝ := fun x => (H x.1)⁻¹ ^ q
  let e : βN → β := fun x =>
    ⟨x.1, le_trans (by exact_mod_cast hN) x.2⟩
  have he_inj : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    change x.1 = y.1
    exact congrArg (fun z : β => z.1) hxy
  have hmajor : Summable (fun x : β => (H x.1)⁻¹ ^ q) := by
    simpa [β] using summable_height_inv_pow_of_one_le hcount hpq
  have hf : Summable f := by
    simpa [f, e, β, βN, Function.comp_def] using
      hmajor.comp_injective he_inj
  let s : γ → Set βN := fun j =>
    {x | x.1 ∈ heightShell H j}
  have hs_unique : ∀ x : βN, ∃! j, x ∈ s j := by
    intro x
    have hxone : 1 ≤ H x.1 :=
      le_trans (by exact_mod_cast hN) x.2
    obtain ⟨n, hn, hxn⟩ := exists_mem_heightShell_of_one_le hxone
    have hNn : N ≤ n := by
      by_contra hnot
      have hlt : n < N := Nat.lt_of_not_ge hnot
      have hstep : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hlt)
      exact (not_lt_of_ge x.2) (lt_of_lt_of_le hxn.2 hstep)
    refine ⟨⟨n, hNn⟩, ?_, ?_⟩
    · exact hxn
    · intro j hj
      apply Subtype.ext
      exact mem_heightShell_unique hj hxn
  have hs_finite : ∀ j : γ, (s j).Finite := by
    intro j
    have hpre : ({x : βN | (x : α) ∈ heightShell H j}).Finite := by
      apply (heightShell_finite hcount (le_trans hN j.property)).preimage
      intro x hx y hy hxy
      exact Subtype.ext hxy
    simpa [s] using hpre
  have hf_nonneg : ∀ x : βN, 0 ≤ f x := by
    intro x
    dsimp [f]
    exact pow_nonneg (inv_nonneg.mpr (le_trans zero_le_one
      (le_trans (by exact_mod_cast hN) x.2))) q
  have hpartition :
      (∑' x : βN, f x) = ∑' j : γ, ∑' x : s j, f x := by
    exact tsum_eq_tsum_partition hf hs_unique
  have hinner_summable : Summable (fun j : γ => ∑' x : s j, f x) := by
    exact ((summable_partition hf_nonneg hs_unique).mp hf).2
  let a : γ → ℝ := fun j =>
    (Set.ncard (heightShell H j) : ℝ) * ((j : ℝ)⁻¹ ^ q)
  have ha_full : Summable (fun n : ℕ =>
      (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) :=
    summable_heightShell_inv_pow_of_lt hcount hpq
  have ha : Summable a := by
    let eγ : {n : ℕ // N ≤ n} ≃ γ :=
      Equiv.subtypeEquiv (Equiv.refl ℕ) (fun _ => by rfl)
    have h := (ha_full.subtype (fun n : ℕ => N ≤ n)).comp_injective
      eγ.symm.injective
    refine h.congr ?_
    intro j
    change (Set.ncard (heightShell H (eγ.symm j : ℕ)) : ℝ) *
        (((eγ.symm j : ℕ) : ℝ)⁻¹ ^ q) = a j
    rfl
  have hseries_eq :
      (∑' j : γ, a j) =
        ∑' n : ℕ, if N ≤ n then
          (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) else 0 := by
    change (∑' j : γ,
        (Set.ncard (heightShell H j) : ℝ) * ((j : ℝ)⁻¹ ^ q)) = _
    simpa [Set.indicator, Set.mem_setOf_eq] using
      (tsum_subtype {n : ℕ | N ≤ n} (fun n : ℕ =>
        (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)))
  have hinner_le : ∀ j : γ, (∑' x : s j, f x) ≤ a j := by
    intro j
    let hs := hs_finite j
    letI : Fintype (s j) := hs.fintype
    have hcard : Fintype.card (s j) = Set.ncard (heightShell H j) := by
      have himage : ((fun x : βN => (x : α)) '' s j) =
          heightShell H j := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          have hxN : (N : ℝ) ≤ H x :=
            le_trans (by exact_mod_cast j.property) hx.1
          refine ⟨⟨x, hxN⟩, hx, rfl⟩
      have himcard : ((fun x : βN => (x : α)) '' s j).ncard =
          (s j).ncard := by
        apply (Set.ncard_image_iff hs).2
        intro x hx y hy hxy
        exact Subtype.ext hxy
      calc
        Fintype.card (s j) = (s j).ncard := Set.fintypeCard_eq_ncard (s j)
        _ = ((fun x : βN => (x : α)) '' s j).ncard := himcard.symm
        _ = Set.ncard (heightShell H j) := by rw [himage]
    change (∑' x : s j, f x) ≤ a j
    rw [tsum_eq_sum (s := Finset.univ) (fun b hb =>
      (hb (Finset.mem_univ b)).elim)]
    calc
      (∑ x : s j, f x) ≤ ∑ x : s j, ((j : ℝ)⁻¹ ^ q) := by
        apply Finset.sum_le_sum
        intro x hx
        have hjpos : 0 < (j : ℕ) := lt_of_lt_of_le
          (show 0 < N by omega) j.property
        exact heightShell_inv_pow_le hjpos x.property
      _ = (Set.ncard (heightShell H j) : ℝ) * ((j : ℝ)⁻¹ ^ q) := by
        simp [Finset.sum_const, hcard]
      _ = a j := rfl
  have hseries_le :
      (∑' j : γ, ∑' x : s j, f x) ≤ ∑' j : γ, a j :=
    hinner_summable.tsum_le_tsum hinner_le ha
  calc
    (∑' x : βN, f x) = ∑' j : γ, ∑' x : s j, f x := hpartition
    _ ≤ ∑' j : γ, a j := hseries_le
    _ = ∑' n : ℕ, if N ≤ n then
        (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) else 0 := hseries_eq
    _ ≤ C * ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := htail hN

/- [derived consequence, paper lines 837--858 and equation
   `eq:summable_matrices`] A summand dominated by a reciprocal height power is
   absolutely summable once the height-counting input is available.  The
   domination is kept as an explicit hypothesis: proving the paper's
   covolume/Jacobian estimate is a separate normalization step. -/
theorem summable_of_abs_le_height_inv_pow
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hpq : p < q)
    {w : α → ℝ} {C : ℝ}
    (hw : ∀ x : α, 1 ≤ H x →
      |w x| ≤ C * (H x)⁻¹ ^ q) :
    Summable (fun x : {x : α // 1 ≤ H x} => w x.1) := by
  have hheight : Summable (fun x : {x : α // 1 ≤ H x} =>
      (H x.1)⁻¹ ^ q) :=
    summable_height_inv_pow_of_one_le hcount hpq
  have habs : Summable (fun x : {x : α // 1 ≤ H x} =>
      |w x.1|) := by
    refine Summable.of_nonneg_of_le
      (f := fun x : {x : α // 1 ≤ H x} =>
        C * (H x.1)⁻¹ ^ q)
      (g := fun x : {x : α // 1 ≤ H x} => |w x.1|)
      (fun x => abs_nonneg _)
      (fun x => hw x.1 x.2)
      (hheight.mul_left C)
  exact Summable.of_norm (by simpa [Real.norm_eq_abs] using habs)

/- [derived consequence, paper lines 837--858] The paper's height is expected
   to be at least one, but the present covolume realization records only
   positivity.  The count bound still makes the sublevel set `H < 1` finite,
   so arbitrary summands on that finite exceptional set can be included. -/
theorem summable_of_abs_le_height_inv_pow_all
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hpq : p < q)
    {w : α → ℝ} {C : ℝ}
    (hw : ∀ x : α, 1 ≤ H x →
      |w x| ≤ C * (H x)⁻¹ ^ q) :
    Summable w := by
  obtain ⟨cₗ, cᵤ, hcₗ, hcᵤ, hcut⟩ := hcount
  have hcount' : HasHeightCountBounds H p := ⟨cₗ, cᵤ, hcₗ, hcᵤ, hcut⟩
  let L : Set α := {x | H x < 1}
  have hL : L.Finite := by
    apply (hcut 1 le_rfl).1.subset
    intro x hx
    change H x ≤ 1
    exact hx.le
  let wL : α → ℝ := L.indicator w
  have hwL_support : (Function.support wL).Finite := by
    apply hL.subset
    intro x hx
    by_contra hxL
    apply hx
    simp [wL, hxL]
  have hwL : Summable wL := summable_of_hasFiniteSupport hwL_support
  have hwS' : Summable ({x : α | 1 ≤ H x}.indicator w) := by
    exact (summable_subtype_iff_indicator (s := {x : α | 1 ≤ H x})).mp
      (summable_of_abs_le_height_inv_pow hcount' hpq hw)
  have hdecomp : w = wL + ({x : α | 1 ≤ H x}.indicator w) := by
    funext x
    by_cases hx : H x < 1
    · simp [wL, L, hx, not_le_of_gt hx]
    · have hxL : x ∉ L := by simpa [L] using hx
      simp [wL, L, hx, hxL, le_of_not_gt hx]
  rw [hdecomp]
  exact hwL.add hwS'

/- [derived consequence, paper lines 837--858 and corollary `co:tail`]
   Quantitative version of the reciprocal-height domination argument.  This is
   the point-counting tail estimate before the paper-specific covolume and
   echelon-weight estimates are substituted. -/
set_option maxHeartbeats 1200000 in
theorem weighted_height_tsum_tail_inv_pow_le
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hpq : p < q)
    {w : α → ℝ} {C : ℝ} (hC : 0 < C)
    (hw : ∀ x : α, 1 ≤ H x →
      |w x| ≤ C * (H x)⁻¹ ^ q) :
    ∃ Ctail : ℝ, 0 < Ctail ∧ ∀ {N : ℕ}, 1 ≤ N →
      (∑' x : {x : α // (N : ℝ) ≤ H x}, |w x.1|) ≤
        Ctail * ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := by
  obtain ⟨C₀, hC₀, htail⟩ := height_tsum_tail_inv_pow_le hcount hpq
  let β := {x : α // 1 ≤ H x}
  have hheight : Summable (fun x : β => (H x.1)⁻¹ ^ q) := by
    simpa [β] using summable_height_inv_pow_of_one_le hcount hpq
  have hweight : Summable (fun x : β => |w x.1|) := by
    simpa only [abs_abs] using
      (summable_of_abs_le_height_inv_pow (w := fun x => |w x|)
        hcount hpq (fun x hx => by simpa only [abs_abs] using hw x hx))
  refine ⟨C * C₀, mul_pos hC hC₀, ?_⟩
  intro N hN
  let βN := {x : α // (N : ℝ) ≤ H x}
  let e : βN → β := fun x =>
    ⟨x.1, le_trans (by exact_mod_cast hN) x.2⟩
  have he_inj : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : β => z.1) hxy
  have hheightN : Summable (fun x : βN => (H x.1)⁻¹ ^ q) :=
    hheight.comp_injective he_inj
  have hweightN : Summable (fun x : βN => |w x.1|) :=
    hweight.comp_injective he_inj
  have hpoint : ∀ x : βN, |w x.1| ≤ C * (H x.1)⁻¹ ^ q := by
    intro x
    exact hw x.1 (le_trans (by exact_mod_cast hN) x.2)
  have hsum_le :
      (∑' x : βN, |w x.1|) ≤
        ∑' x : βN, C * (H x.1)⁻¹ ^ q :=
    hweightN.tsum_le_tsum hpoint (hheightN.mul_left C)
  calc
    (∑' x : βN, |w x.1|) ≤
        ∑' x : βN, C * (H x.1)⁻¹ ^ q := hsum_le
    _ = C * (∑' x : βN, (H x.1)⁻¹ ^ q) :=
      hheightN.tsum_mul_left C
    _ ≤ C * (C₀ * ((N : ℝ) ^ (-((q - p : ℕ) : ℝ)))) := by
      exact mul_le_mul_of_nonneg_left (htail hN) hC.le
    _ = (C * C₀) * ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := by ring

/- [derived consequence, paper lines 837--858 and corollary `co:tail`]
   Signed form of the preceding estimate.  Absolute summability is retained
   in the proof so that the displayed tsum is an ordinary convergent series. -/
set_option maxHeartbeats 1200000 in
theorem weighted_height_tsum_tail_abs_le
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hpq : p < q)
    {w : α → ℝ} {C : ℝ} (hC : 0 < C)
    (hw : ∀ x : α, 1 ≤ H x →
      |w x| ≤ C * (H x)⁻¹ ^ q) :
    ∃ Ctail : ℝ, 0 < Ctail ∧ ∀ {N : ℕ}, 1 ≤ N →
      |∑' x : {x : α // (N : ℝ) ≤ H x}, w x.1| ≤
        Ctail * ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := by
  obtain ⟨Ctail, hCtail, htail⟩ :=
    weighted_height_tsum_tail_inv_pow_le hcount hpq hC hw
  let β := {x : α // 1 ≤ H x}
  have hweight : Summable (fun x : β => |w x.1|) := by
    simpa only [abs_abs] using
      (summable_of_abs_le_height_inv_pow (w := fun x => |w x|)
        hcount hpq (fun x hx => by simpa only [abs_abs] using hw x hx))
  refine ⟨Ctail, hCtail, ?_⟩
  intro N hN
  let βN := {x : α // (N : ℝ) ≤ H x}
  let e : βN → β := fun x =>
    ⟨x.1, le_trans (by exact_mod_cast hN) x.2⟩
  have he_inj : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : β => z.1) hxy
  have hweightN : Summable (fun x : βN => |w x.1|) :=
    hweight.comp_injective he_inj
  calc
    |∑' x : βN, w x.1| = ‖∑' x : βN, w x.1‖ := by
      simp only [Real.norm_eq_abs]
    _ ≤ ∑' x : βN, ‖w x.1‖ := norm_tsum_le_tsum_norm hweightN
    _ = ∑' x : βN, |w x.1| := by
      apply tsum_congr
      intro x
      simp only [Real.norm_eq_abs]
    _ ≤ Ctail * ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := htail hN

/- [derived consequence, paper corollary `co:tail`] The same argument applies
   to the paper's actual summand once its reciprocal-height domination has been
   proved.  This is the interface used by the matrix-counting layer. -/
theorem weighted_height_tail_tendsto_zero
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hpq : p < q)
    {w : α → ℝ} {C : ℝ}
    (hw : ∀ x : α, 1 ≤ H x →
      |w x| ≤ C * (H x)⁻¹ ^ q) :
    Tendsto
      (fun R : ℝ => ∑' x : {x : α // 1 ≤ H x},
        if R ≤ H x.1 then w x.1 else 0)
      atTop (𝓝 0) := by
  let β := {x : α // 1 ≤ H x}
  let g : β → ℝ := fun x => w x.1
  let bound : β → ℝ := fun x => |w x.1|
  have hbound_sum : Summable bound := by
    simpa [bound] using (summable_of_abs_le_height_inv_pow hcount hpq
      (w := fun x => |w x|) (C := C) (fun x hx => by simpa using hw x hx))
  have hpoint : ∀ x : β, Tendsto
      (fun R : ℝ => if R ≤ H x.1 then g x else 0)
      atTop (𝓝 0) := by
    intro x
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop (H x.1)] with R hR
    simp [not_le_of_gt hR]
  have hbound : ∀ᶠ R : ℝ in atTop, ∀ x : β,
      ‖(if R ≤ H x.1 then g x else 0)‖ ≤ bound x := by
    exact Eventually.of_forall (fun R x => by
      by_cases hR : R ≤ H x.1
      · simp [hR, g, bound, Real.norm_eq_abs]
      · simp [hR, bound, Real.norm_eq_abs])
  simpa [g] using
    (tendsto_tsum_of_dominated_convergence hbound_sum hpoint hbound)

/- [derived consequence, paper corollary `co:tail`] Even before the sharper
   quantitative tail exponent is assembled, the reciprocal-height majorant
   gives the qualitative fact that its contribution above a moving height
   cutoff tends to zero.  The cutoff is written as an indicator on the fixed
   positive-height subtype so that Tannery's theorem applies directly. -/
theorem height_inv_pow_tail_tendsto_zero
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hpq : p < q) :
    Tendsto
      (fun R : ℝ => ∑' x : {x : α // 1 ≤ H x},
        if R ≤ H x.1 then (H x.1)⁻¹ ^ q else 0)
      atTop (𝓝 0) := by
  let β := {x : α // 1 ≤ H x}
  let g : β → ℝ := fun x => (H x.1)⁻¹ ^ q
  have hsum : Summable g := by
    simpa [g] using summable_height_inv_pow_of_one_le hcount hpq
  have hpoint : ∀ x : β, Tendsto
      (fun R : ℝ => if R ≤ H x.1 then g x else 0)
      atTop (𝓝 0) := by
    intro x
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop (H x.1)] with R hR
    simp [not_le_of_gt hR]
  have hbound : ∀ᶠ R : ℝ in atTop, ∀ x : β,
      ‖(if R ≤ H x.1 then g x else 0)‖ ≤ g x := by
    exact Eventually.of_forall (fun R x => by
      by_cases hR : R ≤ H x.1
      · have hnonneg : 0 ≤ g x := by
          dsimp [g]
          exact pow_nonneg (inv_nonneg.mpr (le_trans zero_le_one x.2)) q
        simpa [hR, Real.norm_of_nonneg hnonneg]
      · have hnonneg : 0 ≤ g x := by
          dsimp [g]
          exact pow_nonneg (inv_nonneg.mpr (le_trans zero_le_one x.2)) q
        simp [hR]
        exact hnonneg
    )
  simpa [g] using
    (tendsto_tsum_of_dominated_convergence hsum hpoint hbound)

/- The following consequences are parameterized by the height-counting input.
   The source of that input is Schmidt's theorem, but this file does not hide
   it behind an axiom: a future supporting formalization must supply an actual
   proof of the displayed `HasHeightCountBounds` hypothesis. -/
theorem summable_rowSpaceHeight_inv_pow_of_one_le
    {m k q : ℕ}
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    (hmq : m < q) :
    Summable (fun V : {V : Grassmannian K m k //
      1 ≤ rowSpaceHeight V} => (rowSpaceHeight V.1)⁻¹ ^ q) := by
  exact summable_height_inv_pow_of_one_le hcount hmq


/- The intermediate-rank hypothesis in Schmidt's theorem is essential to its
   formulation, but the full-rank stratum is elementary: there is only the
   ambient subspace.  We record this boundary case separately rather than
   forcing it through the imported theorem. -/
theorem grassmannian_fullRank_eq_top {m : ℕ}
    (V : Grassmannian K m m) : V.1 = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  simpa using V.2

instance grassmannian_fullRank_subsingleton (m : ℕ) :
    Subsingleton (Grassmannian K m m) where
  allEq V W := by
    apply Subtype.ext
    rw [grassmannian_fullRank_eq_top V, grassmannian_fullRank_eq_top W]

theorem rowSpaceHeightBall_finite_fullRank {m : ℕ} {T : ℝ} :
    (rowSpaceHeightBall (K := K) (m := m) (k := m) T).Finite := by
  have hsub :
      (rowSpaceHeightBall (K := K) (m := m) (k := m) T).Subsingleton := by
    intro V hV W hW
    exact Subsingleton.elim V W
  exact hsub.finite

theorem grassmannian_zeroRank_eq_bot {m : ℕ}
    (V : Grassmannian K m 0) : V.1 = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  exact V.2

instance grassmannian_zeroRank_subsingleton (m : ℕ) :
    Subsingleton (Grassmannian K m 0) where
  allEq V W := by
    apply Subtype.ext
    rw [grassmannian_zeroRank_eq_bot V, grassmannian_zeroRank_eq_bot W]

theorem rowSpaceHeightBall_finite_zeroRank {m : ℕ} {T : ℝ} :
    (rowSpaceHeightBall (K := K) (m := m) (k := 0) T).Finite := by
  have hsub :
      (rowSpaceHeightBall (K := K) (m := m) (k := 0) T).Subsingleton := by
    intro V hV W hW
    exact Subsingleton.elim V W
  exact hsub.finite

theorem rowSpaceHeightBall_finite
    {m k : ℕ}
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    {T : ℝ} (hT : 1 ≤ T) :
    (rowSpaceHeightBall (K := K) (m := m) (k := k) T).Finite := by
  obtain ⟨cₗ, cᵤ, hcₗ, hcᵤ, hcut⟩ := hcount
  exact (hcut T hT).1

theorem rowSpaceHeightBall_finite_of_intermediate
    {m k : ℕ}
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    {T : ℝ} :
    (rowSpaceHeightBall (K := K) (m := m) (k := k) T).Finite := by
  by_cases hT : 1 ≤ T
  · exact rowSpaceHeightBall_finite hcount hT
  · apply Set.Finite.subset (rowSpaceHeightBall_finite hcount le_rfl)
    intro V hV
    change rowSpaceHeight V ≤ T at hV
    change rowSpaceHeight V ≤ 1
    exact hV.trans (le_of_not_ge hT)

theorem rowSpaceHeightBall_finite_of_rank_le
    {m k : ℕ}
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    (hkm : k ≤ m) {T : ℝ} :
    (rowSpaceHeightBall (K := K) (m := m) (k := k) T).Finite := by
  by_cases hk0 : k = 0
  · subst k
    exact rowSpaceHeightBall_finite_zeroRank
  by_cases hkeq : k = m
  · subst k
    exact rowSpaceHeightBall_finite_fullRank
  · exact rowSpaceHeightBall_finite_of_intermediate hcount

theorem rowSpaceHeightBall_count_upper
    {m k : ℕ}
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m) :
    ∃ cᵤ : ℝ, 0 < cᵤ ∧ ∀ {T : ℝ}, 1 ≤ T →
      (Set.ncard (rowSpaceHeightBall (K := K) (m := m) (k := k) T) : ℝ) ≤
        cᵤ * T ^ m := by
  obtain ⟨cₗ, cᵤ, hcₗ, hcᵤ, hcut⟩ := hcount
  refine ⟨cᵤ, hcᵤ, ?_⟩
  intro T hT
  simpa [rowSpaceHeightBall] using (hcut T hT).2.2

/- The two boundary ranks have one Grassmannian point, so the same upper
   bound is available uniformly for every `k ≤ m`. -/
theorem rowSpaceHeightBall_count_upper_of_rank_le
    {m k : ℕ}
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    (hkm : k ≤ m) :
    ∃ cᵤ : ℝ, 0 < cᵤ ∧ ∀ {T : ℝ}, 1 ≤ T →
      (Set.ncard (rowSpaceHeightBall (K := K) (m := m) (k := k) T) : ℝ) ≤
        cᵤ * T ^ m := by
  by_cases hk0 : k = 0
  · subst k
    refine ⟨1, one_pos, ?_⟩
    intro T hT
    have hcard : Set.ncard
        (rowSpaceHeightBall (K := K) (m := m) (k := 0) T) ≤ 1 :=
      Set.ncard_le_one_of_subsingleton _
    have hcardR :
        (Set.ncard
          (rowSpaceHeightBall (K := K) (m := m) (k := 0) T) : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    exact hcardR.trans (by simpa using (one_le_pow₀ hT))
  by_cases hkm_eq : k = m
  · subst k
    refine ⟨1, one_pos, ?_⟩
    intro T hT
    have hcard : Set.ncard
        (rowSpaceHeightBall (K := K) (m := m) (k := m) T) ≤ 1 :=
      Set.ncard_le_one_of_subsingleton _
    have hcardR :
        (Set.ncard
          (rowSpaceHeightBall (K := K) (m := m) (k := m) T) : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    exact hcardR.trans (by simpa using (one_le_pow₀ hT))
  exact rowSpaceHeightBall_count_upper (K := K) hcount

theorem heightBoundedRowSpaces_finite
    {m k : ℕ}
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    {C T : ℝ} (hC : 1 ≤ C) (hT : 1 ≤ T) :
    (heightBoundedRowSpaces (K := K) (m := m) (k := k) C T).Finite := by
  apply rowSpaceHeightBall_finite hcount
  calc
    (1 : ℝ) = 1 * 1 := by norm_num
    _ ≤ C * T ^ (k * degree K) :=
      mul_le_mul hC (one_le_pow₀ hT) (by norm_num)
        (le_trans (by norm_num) hC)

theorem heightBoundedRowSpaces_count_upper
    {m k : ℕ}
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m) :
    ∃ cᵤ : ℝ, 0 < cᵤ ∧ ∀ {C T : ℝ}, 1 ≤ C → 1 ≤ T →
      (Set.ncard (heightBoundedRowSpaces (K := K) (m := m) (k := k) C T) : ℝ) ≤
        cᵤ * (C * T ^ (k * degree K)) ^ m := by
  obtain ⟨cᵤ, hcᵤ, hcount'⟩ :=
    rowSpaceHeightBall_count_upper (K := K) hcount
  refine ⟨cᵤ, hcᵤ, ?_⟩
  intro C T hC hT
  have hB : (1 : ℝ) ≤ C * T ^ (k * degree K) := by
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ C * T ^ (k * degree K) :=
        mul_le_mul hC (one_le_pow₀ hT) (by norm_num)
          (le_trans (by norm_num) hC)
  simpa [heightBoundedRowSpaces] using hcount' hB

theorem heightBoundedRowSpaces_count_upper_of_rank_le
    {m k : ℕ}
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    (hkm : k ≤ m) :
    ∃ cᵤ : ℝ, 0 < cᵤ ∧ ∀ {C T : ℝ}, 1 ≤ C → 1 ≤ T →
      (Set.ncard (heightBoundedRowSpaces (K := K) (m := m) (k := k) C T) : ℝ) ≤
        cᵤ * (C * T ^ (k * degree K)) ^ m := by
  by_cases hk0 : k = 0
  · subst k
    refine ⟨1, one_pos, ?_⟩
    intro C T hC hT
    have hcard : Set.ncard
        (heightBoundedRowSpaces (K := K) (m := m) (k := 0) C T) ≤ 1 := by
      apply Set.ncard_le_one_of_subsingleton
    have hcardR :
        (Set.ncard
          (heightBoundedRowSpaces (K := K) (m := m) (k := 0) C T) : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    have hbase : (1 : ℝ) ≤ C * T ^ (0 * degree K) := by
      simp only [zero_mul, pow_zero, mul_one]
      exact hC
    exact hcardR.trans (by simpa using (one_le_pow₀ hbase :
      (1 : ℝ) ≤ (C * T ^ (0 * degree K)) ^ m))
  by_cases hkm_eq : k = m
  · subst k
    refine ⟨1, one_pos, ?_⟩
    intro C T hC hT
    have hcard : Set.ncard
        (heightBoundedRowSpaces (K := K) (m := m) (k := m) C T) ≤ 1 := by
      apply Set.ncard_le_one_of_subsingleton
    have hcardR :
        (Set.ncard
          (heightBoundedRowSpaces (K := K) (m := m) (k := m) C T) : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    have hbase : (1 : ℝ) ≤ C * T ^ (m * degree K) := by
      calc
        (1 : ℝ) = 1 * 1 := by norm_num
        _ ≤ C * T ^ (m * degree K) :=
          mul_le_mul hC (one_le_pow₀ hT) (by norm_num)
            (le_trans (by norm_num) hC)
    exact hcardR.trans (by simpa using (one_le_pow₀ hbase :
      (1 : ℝ) ≤ (C * T ^ (m * degree K)) ^ m))
  exact heightBoundedRowSpaces_count_upper (K := K) hcount

end

end Katznelson
