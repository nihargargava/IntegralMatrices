import Katznelson.Counting.UniformHeightTail

/-!
# Literal absolute height tail

This module exposes the height tail in the termwise-absolute form used in
`papers/katznelson.tex`, Corollary `co:tail` (lines 1160--1169) and equation
`eq:nonrequired_eq` (lines 1653--1665).  In contrast with the older
assembly interface, the absolute value here is inside the `tsum`.
-/

namespace Katznelson

open scoped BigOperators Classical NumberField

/- [Lean infrastructure] Matrix norms are non-global in Mathlib.  These are
the same Frobenius-norm instances used to define the exact manuscript family
`boundedRowSpaces`; no norm or normalization is changed here. -/
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

/- [derived consequence of paper Corollary `co:tail`, lines 1160--1169,
and its use in equation `eq:nonrequired_eq`, lines 1653--1665] This is the
row-space form obtained through the proved exact family identity
`echelon_calF_image_eq_boundedRowSpaces`.  The cutoff is retained literally as
`X = Clower * T ^ degree K`.  Most importantly, the left side is the `tsum`
of the absolute value of every omitted main-term summand, not the absolute
value of their `tsum`.

The only external arithmetic input is the explicitly supplied and attributed
Schmidt interface `HasHeightCountBounds`; all geometric and summability inputs
are proved declarations imported from `UniformHeightTail`. -/
set_option maxHeartbeats 2400000 in
theorem exists_uniform_boundedRowSpaces_mainConstant_complement_abs_sum_tail_with_cutoff
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hnm : m < n) (hkn : k ≤ n) (hkm : k ≤ m)
    (hk : 0 < k) {Csup : ℝ} (hCsup : 0 < Csup)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    {f : M n m (K_ℝ[K]) → ℝ} {C : ℝ} (hC : 0 < C)
    (hdom : ∀ V : Grassmannian K m k, 1 ≤ rowSpaceHeight V →
      |(rowSpaceHeight V)⁻¹ ^ n * rowMatrixSubspaceIntegral V n f| ≤
        C * (rowSpaceHeight V)⁻¹ ^ n) :
    ∃ Clower Ctail : ℝ, 0 < Clower ∧ 0 < Ctail ∧
      ∀ T : ℝ, 2 ≤ T →
        ∃ X : ℝ, X = Clower * T ^ degree K ∧ 0 < X ∧
          (∀ V : Grassmannian K m k,
            V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
              Csup T → X ≤ rowSpaceHeight V) ∧
          (∑' V : {V : Grassmannian K m k //
              V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
                Csup T},
            |(rowMatrixLatticeCovolume V.1 n)⁻¹ *
              rowMatrixSubspaceIntegral V.1 n f|) ≤
            Ctail * T ^ (-(degree K : ℤ)) := by
  obtain ⟨Clower, hClower, hheight⟩ :=
    exists_uniform_boundedRowSpaces_complement_height_lower_bound_of_fiekerStehle
      (K := K) (n := n) (m := m) (k := k) (Csup := Csup)
      hkn hkm hk hCsup
  let g : Grassmannian K m k → ℝ := fun V ↦
    (rowMatrixLatticeCovolume V n)⁻¹ * rowMatrixSubspaceIntegral V n f
  have hgdom : ∀ V : Grassmannian K m k, 1 ≤ rowSpaceHeight V →
      |g V| ≤ C * (rowSpaceHeight V)⁻¹ ^ n := by
    intro V hV
    simpa [g, rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow, inv_pow] using
      hdom V hV
  obtain ⟨Creal, hCreal, hrealTail⟩ :=
    weighted_height_tsum_tail_real_inv_pow_le hcount hnm hC hgdom
  have habs : Summable (fun V : Grassmannian K m k ↦ |g V|) := by
    apply summable_of_abs_le_height_inv_pow_all hcount hnm
    intro V hV
    simpa only [abs_abs] using hgdom V hV
  let Ctail : ℝ := Creal * (Clower ^ (n - m))⁻¹
  have hCtail : 0 < Ctail := by
    dsimp [Ctail]
    positivity
  refine ⟨Clower, Ctail, hClower, hCtail, ?_⟩
  intro T hTtwo
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) hTtwo
  let X : ℝ := Clower * T ^ degree K
  have hX : 0 < X := by
    dsimp [X]
    positivity
  have houtside : ∀ V : Grassmannian K m k,
      V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T →
        X ≤ rowSpaceHeight V := by
    intro V hV
    exact hheight T hT V hV
  have hcompl :
      (∑' V : {V : Grassmannian K m k //
          V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
            Csup T}, |g V.1|) ≤
        ∑' V : {V : Grassmannian K m k // X ≤ rowSpaceHeight V},
          |g V.1| := by
    let beta := {V : Grassmannian K m k //
      V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T}
    let betaX := {V : Grassmannian K m k // X ≤ rowSpaceHeight V}
    let e : beta → betaX := fun V ↦ ⟨V.1, houtside V.1 V.2⟩
    have he : Function.Injective e := by
      intro V W hVW
      apply Subtype.ext
      exact congrArg (fun U : betaX ↦ U.1) hVW
    have hsumBeta : Summable (fun V : beta ↦ |g V.1|) :=
      habs.comp_injective Subtype.val_injective
    have hsumBetaX : Summable (fun V : betaX ↦ |g V.1|) :=
      habs.comp_injective Subtype.val_injective
    exact hsumBeta.tsum_le_tsum_of_inj e he
      (fun V _ ↦ abs_nonneg (g V)) (fun _ ↦ le_rfl) hsumBetaX
  have htailX :
      (∑' V : {V : Grassmannian K m k // X ≤ rowSpaceHeight V},
        |g V.1|) ≤ Creal * X ^ (-((n - m : ℕ) : ℝ)) :=
    hrealTail hX
  have hscale :
      X ^ (-((n - m : ℕ) : ℝ)) =
        (Clower ^ (n - m))⁻¹ *
          (T ^ (degree K * (n - m)))⁻¹ := by
    dsimp [X]
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    rw [mul_pow, pow_mul]
    rw [mul_inv_rev]
    ring
  have hcodim : 1 ≤ n - m := by omega
  have hexponents : degree K ≤ degree K * (n - m) := by
    calc
      degree K = degree K * 1 := by rw [mul_one]
      _ ≤ degree K * (n - m) := Nat.mul_le_mul_left _ hcodim
  have hpow : T ^ degree K ≤ T ^ (degree K * (n - m)) :=
    pow_le_pow_right₀ (le_trans (by norm_num) hTtwo) hexponents
  have hdecay :
      (T ^ (degree K * (n - m)))⁻¹ ≤ T ^ (-(degree K : ℤ)) := by
    rw [← inv_nat_pow_eq_zpow_neg_nat T (degree K)]
    exact (inv_le_inv₀ (pow_pos hT _) (pow_pos hT _)).2 hpow
  refine ⟨X, rfl, hX, houtside, ?_⟩
  calc
    (∑' V : {V : Grassmannian K m k //
        V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
          Csup T},
      |(rowMatrixLatticeCovolume V.1 n)⁻¹ *
        rowMatrixSubspaceIntegral V.1 n f|) =
        ∑' V : {V : Grassmannian K m k //
          V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
            Csup T}, |g V.1| := by rfl
    _ ≤ ∑' V : {V : Grassmannian K m k // X ≤ rowSpaceHeight V},
        |g V.1| := hcompl
    _ ≤ Creal * X ^ (-((n - m : ℕ) : ℝ)) := htailX
    _ = Ctail * (T ^ (degree K * (n - m)))⁻¹ := by
      rw [hscale]
      dsimp [Ctail]
      ring
    _ ≤ Ctail * T ^ (-(degree K : ℤ)) :=
      mul_le_mul_of_nonneg_left hdecay hCtail.le

/- [derived consequence of the preceding formalization of paper Corollary
`co:tail`, lines 1160--1169] This is the manuscript-facing form consumed at
lines 1653--1665: the cutoff witness is hidden, but `Ctail` remains outside
the scale quantifier and the absolute value remains inside the `tsum`. -/
theorem exists_uniform_boundedRowSpaces_mainConstant_complement_abs_sum_tail
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hnm : m < n) (hkn : k ≤ n) (hkm : k ≤ m)
    (hk : 0 < k) {Csup : ℝ} (hCsup : 0 < Csup)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    {f : M n m (K_ℝ[K]) → ℝ} {C : ℝ} (hC : 0 < C)
    (hdom : ∀ V : Grassmannian K m k, 1 ≤ rowSpaceHeight V →
      |(rowSpaceHeight V)⁻¹ ^ n * rowMatrixSubspaceIntegral V n f| ≤
        C * (rowSpaceHeight V)⁻¹ ^ n) :
    ∃ Ctail : ℝ, 0 < Ctail ∧ ∀ T : ℝ, 2 ≤ T →
      (∑' V : {V : Grassmannian K m k //
          V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
            Csup T},
        |(rowMatrixLatticeCovolume V.1 n)⁻¹ *
          rowMatrixSubspaceIntegral V.1 n f|) ≤
        Ctail * T ^ (-(degree K : ℤ)) := by
  obtain ⟨Clower, Ctail, hClower, hCtail, htail⟩ :=
    exists_uniform_boundedRowSpaces_mainConstant_complement_abs_sum_tail_with_cutoff
      hnm hkn hkm hk hCsup hcount hC hdom
  refine ⟨Ctail, hCtail, ?_⟩
  intro T hT
  obtain ⟨X, hX, hXpos, houtside, htailT⟩ := htail T hT
  exact htailT

/- [derived consequence of paper Corollary `co:tail`, lines 1160--1169,
and equation `eq:nonrequired_eq`, lines 1653--1665] The literal termwise
tail above implies the absolute error form consumed by the final finite-family
assembly.  This bridge uses only the exact decomposition of `mainConstant`
into the chosen finite family and its complement, followed by the triangle
inequality for a summable series. -/
theorem exists_uniform_boundedRowSpaces_mainConstant_tail_abs_le_literal
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hnm : m < n) (hkn : k ≤ n) (hkm : k ≤ m)
    (hk : 0 < k) {Csup : ℝ} (hCsup : 0 < Csup)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    {f : M n m (K_ℝ[K]) → ℝ} {C : ℝ} (hC : 0 < C)
    (hdom : ∀ V : Grassmannian K m k, 1 ≤ rowSpaceHeight V →
      |(rowSpaceHeight V)⁻¹ ^ n * rowMatrixSubspaceIntegral V n f| ≤
        C * (rowSpaceHeight V)⁻¹ ^ n) :
    ∃ Ctail : ℝ, 0 < Ctail ∧ ∀ T : ℝ, 2 ≤ T →
      ∀ [Fintype (boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
        Csup T)],
        |mainConstant n m k f -
            finiteRowMatrixMainTermSum
              (boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
                Csup T) f| ≤
          Ctail * T ^ (-(degree K : ℤ)) := by
  obtain ⟨Ctail, hCtail, htail⟩ :=
    exists_uniform_boundedRowSpaces_mainConstant_complement_abs_sum_tail
      hnm hkn hkm hk hCsup hcount hC hdom
  refine ⟨Ctail, hCtail, ?_⟩
  intro T hT inst
  let B : Set (Grassmannian K m k) :=
    boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T
  let g : Grassmannian K m k → ℝ := fun V =>
    (rowMatrixLatticeCovolume V n)⁻¹ * rowMatrixSubspaceIntegral V n f
  have hsum : Summable g := by
    simpa [g] using
      summable_mainConstant_terms_of_height_count hnm hcount hC hdom
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl B
  change (∑' V : B, g V.1) +
      (∑' V : {V : Grassmannian K m k // V ∉ B}, g V.1) =
        ∑' V : Grassmannian K m k, g V at hsplit
  have hdecomp :
      mainConstant n m k f =
        finiteRowMatrixMainTermSum B f +
          ∑' V : {V : Grassmannian K m k // V ∉ B}, g V.1 := by
    simpa [mainConstant, finiteRowMatrixMainTermSum, g] using hsplit.symm
  have hcomplSummable : Summable
      (fun V : {V : Grassmannian K m k // V ∉ B} => g V.1) :=
    hsum.comp_injective Subtype.val_injective
  calc
    |mainConstant n m k f - finiteRowMatrixMainTermSum B f| =
        |∑' V : {V : Grassmannian K m k // V ∉ B}, g V.1| := by
      rw [hdecomp]
      ring_nf
    _ ≤ ∑' V : {V : Grassmannian K m k // V ∉ B}, |g V.1| := by
      simpa only [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm hcomplSummable.norm
    _ ≤ Ctail * T ^ (-(degree K : ℤ)) := by
      simpa [B, g] using htail T hT

end Katznelson
