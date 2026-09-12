import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

/-!
# Error-scale assembly for the fixed-rank theorem

This file contains only the elementary arithmetic used when the geometric and
counting estimates in the proof of `th:main` are assembled.  In particular,
none of the hypotheses below asserts a radius, lower-rank, or height-tail
estimate: those estimates remain explicit inputs supplied by their faithful
formalizations.

The paper-facing expressions retain the manuscript's integer power

`T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ))`

and its exceptional scale `T⁻¹ * Real.log T`.
-/

namespace Katznelson

/- [Lean infrastructure] Elementary positivity for the logarithmic factor
used throughout the error assembly. -/
theorem one_add_log_nonneg_of_one_le {T : ℝ} (hT : 1 ≤ T) :
    0 ≤ 1 + Real.log T := by
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  linarith

/- [Lean infrastructure] The standard inequality `log T ≤ T - 1`, used only
to absorb one logarithm when at least two reciprocal powers of `T` are
available. -/
theorem one_add_log_le_self_of_pos {T : ℝ} (hT : 0 < T) :
    1 + Real.log T ≤ T := by
  linarith [Real.log_le_sub_one_of_pos hT]

/- [Lean infrastructure] If two or more reciprocal powers are present, the
factor `1 + log T` costs at most one of them.  Integer powers are used because
that is the representation already used for the manuscript's lower-rank
exponent in `MainTheorems.lean`. -/
theorem one_add_log_mul_zpow_neg_nat_le_inv
    {T : ℝ} {q : ℕ} (hT : 1 ≤ T) (hq : 2 ≤ q) :
    (1 + Real.log T) * T ^ (-((q : ℕ) : ℤ)) ≤ T⁻¹ := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hpow_nonneg : 0 ≤ T ^ (-((q : ℕ) : ℤ)) :=
    zpow_nonneg hTpos.le _
  have hexponent : (1 : ℤ) - (q : ℤ) ≤ -1 := by
    have hq' : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
    omega
  calc
    (1 + Real.log T) * T ^ (-((q : ℕ) : ℤ)) ≤
        T * T ^ (-((q : ℕ) : ℤ)) :=
      mul_le_mul_of_nonneg_right (one_add_log_le_self_of_pos hTpos)
        hpow_nonneg
    _ = T ^ ((1 : ℤ) - (q : ℤ)) := by
      calc
        T * T ^ (-((q : ℕ) : ℤ)) =
            T ^ (1 : ℤ) * T ^ (-((q : ℕ) : ℤ)) := by rw [zpow_one]
        _ = T ^ ((1 : ℤ) + -((q : ℕ) : ℤ)) := by
          rw [← zpow_add₀ hTpos.ne']
        _ = T ^ ((1 : ℤ) - (q : ℤ)) := by ring_nf
    _ ≤ T ^ (-1 : ℤ) := zpow_le_zpow_right₀ hT hexponent
    _ = T⁻¹ := by rw [zpow_neg_one]

/- [derived consequence] In the non-exceptional range of the proof of
`th:main` (paper lines 1641--1651), the corrected lower-rank exponent from
line 1682 has absolute value at least two.  The statement keeps the paper's
criterion `(n-m) d k > 1` literally visible. -/
theorem fixedRankLowerExponent_two_le_of_nonexceptional
    {n m k d : ℕ} (hnm : m < n) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hnonexceptional : 1 < (n - m) * d * k) :
    2 ≤ d * (n - m + k - 1) := by
  by_cases hkone : k = 1
  · subst k
    have htwo : 2 ≤ (n - m) * d := by
      exact (Nat.succ_le_iff).2 (by simpa using hnonexceptional)
    simpa [Nat.mul_comm] using htwo
  · have hktwo : 2 ≤ k := by omega
    have hgap : 1 ≤ n - m := by omega
    have hsum : 2 ≤ n - m + k - 1 := by omega
    calc
      2 = 1 * 2 := by norm_num
      _ ≤ d * (n - m + k - 1) := Nat.mul_le_mul hd hsum

/- [derived consequence] This is the precise absorption claimed after
`le:low_rank_terms` at paper line 1682 in the non-exceptional range declared
at line 1644.  No lower-rank estimate is assumed here; only its displayed
scale is compared with `T⁻¹`. -/
theorem lowerRankErrorScale_le_inv_of_nonexceptional
    {n m k d : ℕ} {T : ℝ} (hT : 1 ≤ T) (hnm : m < n)
    (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hnonexceptional : 1 < (n - m) * d * k) :
    (1 + Real.log T) *
        T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) ≤ T⁻¹ := by
  have hq : 2 ≤ d * (n - m + k - 1) :=
    fixedRankLowerExponent_two_le_of_nonexceptional hnm hk hd
      hnonexceptional
  have hbound := one_add_log_mul_zpow_neg_nat_le_inv
    (T := T) (q := d * (n - m + k - 1)) hT hq
  have hexponent :
      -(((d * (n - m + k - 1) : ℕ) : ℤ)) =
        -(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_mul]
    ring
  rw [← hexponent]
  exact hbound

/- [derived consequence] The height-tail scale `T⁻ᵈ` in paper
`eq:nonrequired_eq`, lines 1653--1665, is at most `T⁻¹` for positive number
field degree and `T ≥ 1`. -/
theorem heightTailScale_le_inv
    {d : ℕ} {T : ℝ} (hT : 1 ≤ T) (hd : 1 ≤ d) :
    T ^ (-(d : ℤ)) ≤ T⁻¹ := by
  rw [← zpow_neg_one]
  apply zpow_le_zpow_right₀ hT
  have hd' : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  omega

/- [Lean infrastructure] A bound for the finite radius sum can be multiplied
by the explicit `1/T` from paper equation `eq:ineq212` (lines 1689--1697)
without changing its provenance. -/
theorem radiusError_div_le
    {radius C_radius C_riemann T : ℝ} (hT : 0 ≤ T)
    (hC_riemann : 0 ≤ C_riemann)
    (hradius : radius ≤ C_radius) :
    C_riemann * radius / T ≤ C_riemann * C_radius / T := by
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hradius hC_riemann) hT

/- [derived consequence] Arithmetic assembly of the three displayed error
terms in paper lines 1653--1697.  The lower-rank, tail, and radius estimates
are not manufactured here: this theorem merely combines their exact scales
after they have been proved elsewhere. -/
theorem fixedRankErrorTerms_le_inv_of_nonexceptional
    {n m k d : ℕ} {T C_radius C_lower C_tail : ℝ}
    (hT : 1 ≤ T) (hnm : m < n) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hnonexceptional : 1 < (n - m) * d * k)
    (hC_lower : 0 ≤ C_lower)
    (hC_tail : 0 ≤ C_tail) :
    C_radius / T +
          C_lower * ((1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ))) +
        C_tail * T ^ (-(d : ℤ)) ≤
      (C_radius + C_lower + C_tail) / T := by
  have hlower := lowerRankErrorScale_le_inv_of_nonexceptional
    hT hnm hk hd hnonexceptional
  have htail := heightTailScale_le_inv (T := T) hT hd
  calc
    C_radius / T +
          C_lower * ((1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ))) +
        C_tail * T ^ (-(d : ℤ)) ≤
        C_radius / T + C_lower * T⁻¹ + C_tail * T⁻¹ := by
      exact add_le_add
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlower hC_lower))
        (mul_le_mul_of_nonneg_left htail hC_tail)
    _ = (C_radius + C_lower + C_tail) / T := by
      rw [div_eq_mul_inv]
      ring

/- [derived consequence] Paper-facing wrapper for lines 1641--1697.  Each
mathematical estimate is an explicit hypothesis, while the conclusion is the
single `C/T` error required by `eq:required_eq` in the non-exceptional case. -/
theorem fixedRankError_le_inv_of_nonexceptional_bounds
    {n m k d : ℕ}
    {T E E_radius E_lower E_tail C_radius C_lower C_tail : ℝ}
    (hT : 1 ≤ T) (hnm : m < n) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hnonexceptional : 1 < (n - m) * d * k)
    (hC_lower : 0 ≤ C_lower)
    (hC_tail : 0 ≤ C_tail)
    (hsplit : E ≤ E_radius + E_lower + E_tail)
    (hradius : E_radius ≤ C_radius / T)
    (hlower : E_lower ≤ C_lower * ((1 + Real.log T) *
      T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ))))
    (htail : E_tail ≤ C_tail * T ^ (-(d : ℤ))) :
    E ≤ (C_radius + C_lower + C_tail) / T := by
  calc
    E ≤ E_radius + E_lower + E_tail := hsplit
    _ ≤ C_radius / T +
          C_lower * ((1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ))) +
        C_tail * T ^ (-(d : ℤ)) :=
      add_le_add (add_le_add hradius hlower) htail
    _ ≤ (C_radius + C_lower + C_tail) / T :=
      fixedRankErrorTerms_le_inv_of_nonexceptional hT hnm hk hd
        hnonexceptional hC_lower hC_tail

/- [Lean infrastructure] Exact bridge from the integer-power representation
used for lower-rank exponents to the manuscript's exceptional notation
`T⁻¹ log T` (paper line 1651). -/
theorem zpow_neg_one_mul_log_eq_inv_mul_log (T : ℝ) :
    T ^ (-1 : ℤ) * Real.log T = T⁻¹ * Real.log T := by
  rw [zpow_neg_one]

/- [Lean infrastructure] The manuscript's `T⁻¹ log T` is equivalently the
usual quotient `(log T)/T`; this equality prevents a notation change from
being hidden in a later asymptotic wrapper. -/
theorem inv_mul_log_eq_log_div (T : ℝ) :
    T⁻¹ * Real.log T = Real.log T / T := by
  rw [div_eq_mul_inv, mul_comm]

/- [Lean infrastructure] On the manuscript's exact range `T ≥ 2` (paper
lines 157--169), one has `log T ≥ 1/2`.  The deliberately coarse factor two
avoids introducing a decimal approximation or a hidden larger threshold. -/
theorem one_le_two_mul_log_of_two_le {T : ℝ} (hT : 2 ≤ T) :
    1 ≤ 2 * Real.log T := by
  have hlog_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog_mono : Real.log 2 ≤ Real.log T :=
    Real.log_le_log (by norm_num) hT
  linarith

/- [derived consequence] Explicit comparison between the `1 + log T`
factor arising in `le:low_rank_terms` (line 1682) and the paper's exceptional
`T⁻¹ log T` scale announced at line 1651 and treated at lines 1716--1724. -/
theorem one_add_log_mul_zpow_neg_one_le_three_inv_mul_log
    {T : ℝ} (hT : 2 ≤ T) :
    (1 + Real.log T) * T ^ (-1 : ℤ) ≤
      3 * (T⁻¹ * Real.log T) := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hlog : 1 ≤ 2 * Real.log T := one_le_two_mul_log_of_two_le hT
  have hinv_nonneg : 0 ≤ T⁻¹ := inv_nonneg.mpr hTpos.le
  calc
    (1 + Real.log T) * T ^ (-1 : ℤ) =
        T⁻¹ * (1 + Real.log T) := by
      rw [zpow_neg_one]
      ring
    _ ≤ T⁻¹ * (3 * Real.log T) := by
      apply mul_le_mul_of_nonneg_left _ hinv_nonneg
      linarith
    _ = 3 * (T⁻¹ * Real.log T) := by ring

/- [derived consequence] In the exceptional dimensions singled out at paper
lines 1716--1724, the corrected lower-rank scale specializes exactly to
`(1 + log T) T⁻¹`.  The dimension equalities remain explicit in the
interface. -/
theorem lowerRankErrorScale_eq_exceptional
    {n m k d : ℕ} (T : ℝ) (hn : n = m + 1) (hk : k = 1) (hd : d = 1) :
    (1 + Real.log T) *
        T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) =
      (1 + Real.log T) * T⁻¹ := by
  subst n
  subst k
  subst d
  have hexponent : m + 1 - m + 1 - 1 = 1 := by omega
  rw [hexponent]
  norm_num

/- [derived consequence] The reciprocal scale `T⁻¹` (hence also the
degree-one height tail and an ordinary radius error divided by `T`) is
absorbed by the manuscript's exceptional `T⁻¹ log T` scale beyond the
exact manuscript threshold `T ≥ 2`. -/
theorem inv_le_two_mul_inv_mul_log_of_two_le
    {T : ℝ} (hT : 2 ≤ T) :
    T⁻¹ ≤ 2 * (T⁻¹ * Real.log T) := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hlog : 1 ≤ 2 * Real.log T := one_le_two_mul_log_of_two_le hT
  calc
    T⁻¹ = T⁻¹ * 1 := by ring
    _ ≤ T⁻¹ * (2 * Real.log T) :=
      mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hTpos.le)
    _ = 2 * (T⁻¹ * Real.log T) := by ring

/- [derived consequence] Arithmetic assembly for the exceptional branch of
paper lines 1641--1697 and 1716--1724.  `C_exceptional` represents the direct
rank-one estimate discussed in `ss:log_term`; all four analytic estimates
remain explicit inputs in the wrapper below. -/
theorem fixedRankErrorTerms_le_inv_log_of_exceptional
    {n m k d : ℕ}
    {T C_exceptional C_radius C_lower C_tail : ℝ}
    (hT : 2 ≤ T) (hn : n = m + 1) (hk : k = 1) (hd : d = 1)
    (hC_radius : 0 ≤ C_radius) (hC_lower : 0 ≤ C_lower)
    (hC_tail : 0 ≤ C_tail) :
    C_exceptional * (T⁻¹ * Real.log T) + C_radius / T +
          C_lower * ((1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ))) +
        C_tail * T ^ (-(d : ℤ)) ≤
      (C_exceptional + 2 * C_radius + 3 * C_lower + 2 * C_tail) *
        (T⁻¹ * Real.log T) := by
  let exceptionalScale : ℝ := T⁻¹ * Real.log T
  have hinv_le : T⁻¹ ≤ 2 * exceptionalScale := by
    simpa [exceptionalScale] using inv_le_two_mul_inv_mul_log_of_two_le hT
  have hradius : C_radius / T ≤ C_radius * (2 * exceptionalScale) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv_le hC_radius
  have hlowerScale :
      (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) ≤
        3 * exceptionalScale := by
    rw [lowerRankErrorScale_eq_exceptional T hn hk hd]
    simpa [exceptionalScale] using
      one_add_log_mul_zpow_neg_one_le_three_inv_mul_log hT
  have hlower :
      C_lower * ((1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ))) ≤
        C_lower * (3 * exceptionalScale) :=
    mul_le_mul_of_nonneg_left hlowerScale hC_lower
  have htailScale : T ^ (-(d : ℤ)) ≤ 2 * exceptionalScale := by
    calc
      T ^ (-(d : ℤ)) = T⁻¹ := by
        rw [hd]
        norm_num
      _ ≤ 2 * exceptionalScale := hinv_le
  have htail : C_tail * T ^ (-(d : ℤ)) ≤
      C_tail * (2 * exceptionalScale) :=
    mul_le_mul_of_nonneg_left htailScale hC_tail
  calc
    C_exceptional * (T⁻¹ * Real.log T) + C_radius / T +
          C_lower * ((1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ))) +
        C_tail * T ^ (-(d : ℤ)) ≤
        C_exceptional * exceptionalScale + C_radius * (2 * exceptionalScale) +
          C_lower * (3 * exceptionalScale) +
            C_tail * (2 * exceptionalScale) := by
      exact add_le_add (add_le_add (add_le_add (by rfl) hradius) hlower) htail
    _ = (C_exceptional + 2 * C_radius + 3 * C_lower + 2 * C_tail) *
        (T⁻¹ * Real.log T) := by
      dsimp [exceptionalScale]
      ring

/- [derived consequence] Paper-facing exceptional wrapper.  It combines a
direct degree-one rank-one estimate from `ss:log_term`, an optional ordinary
radius error, the displayed lower-rank scale, and the degree-one height tail.
No one of those mathematical estimates is assumed implicitly. -/
theorem fixedRankError_le_inv_log_of_exceptional_bounds
    {n m k d : ℕ}
    {T E E_exceptional E_radius E_lower E_tail : ℝ}
    {C_exceptional C_radius C_lower C_tail : ℝ}
    (hT : 2 ≤ T) (hn : n = m + 1) (hk : k = 1) (hd : d = 1)
    (hC_radius : 0 ≤ C_radius) (hC_lower : 0 ≤ C_lower)
    (hC_tail : 0 ≤ C_tail)
    (hsplit : E ≤ E_exceptional + E_radius + E_lower + E_tail)
    (hexceptional :
      E_exceptional ≤ C_exceptional * (T⁻¹ * Real.log T))
    (hradius : E_radius ≤ C_radius / T)
    (hlower : E_lower ≤ C_lower * ((1 + Real.log T) *
      T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ))))
    (htail : E_tail ≤ C_tail * T ^ (-(d : ℤ))) :
    E ≤ (C_exceptional + 2 * C_radius + 3 * C_lower + 2 * C_tail) *
      (T⁻¹ * Real.log T) := by
  calc
    E ≤ E_exceptional + E_radius + E_lower + E_tail := hsplit
    _ ≤ C_exceptional * (T⁻¹ * Real.log T) + C_radius / T +
          C_lower * ((1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ))) +
        C_tail * T ^ (-(d : ℤ)) :=
      add_le_add (add_le_add (add_le_add hexceptional hradius) hlower) htail
    _ ≤ (C_exceptional + 2 * C_radius + 3 * C_lower + 2 * C_tail) *
        (T⁻¹ * Real.log T) :=
      fixedRankErrorTerms_le_inv_log_of_exceptional hT hn hk hd
        hC_radius hC_lower hC_tail

end Katznelson
