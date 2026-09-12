import Katznelson.MainTheorems

/-!
# Uniform height tails for the fixed-rank argument

This module repairs the order of quantifiers in the height-tail interface used
in the final fixed-rank assembly.  Both the geometric cutoff constant and the
Schmidt-tail constant are chosen before the scale `T`.  The paper's real
cutoff `X = C_lower * T ^ degree K` remains explicit; a proved floor bridge
records the natural cutoff consumed by the ordinary height shells.

The mathematical inputs are the proved raw-Euclidean Fieker--Stehlé product
bound in `Counting/FiekerStehle.lean` and the explicitly supplied
`HasHeightCountBounds`.  No additional geometric estimate is assumed here.
-/

namespace Katznelson

open Filter MeasureTheory
open scoped BigOperators Classical NumberField Topology

/- [Lean infrastructure] Matrix norms are non-global in Mathlib.  This is the
same Frobenius-norm instance used by `MainTheorems.lean`; it is needed only to
elaborate the manuscript family `calF`/`boundedRowSpaces`, and introduces no
new norm or normalization. -/
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

/- [Lean infrastructure for paper `le:lower_bound_not_in_F` and `co:tail`,
lines 1132--1169] The manuscript cutoff `X` is real, while Schmidt's ordinary
height shells are indexed by naturals.  This lower-rounding bridge makes the
comparison explicit.  When `X ≥ 1`, the selected `N` is a usable lower
height cutoff; for `0 < X < 1`, the later tail proof separately absorbs the
finite initial range. -/
theorem exists_nat_height_cutoff_below_comparable (X : ℝ) (hX : 0 < X) :
    ∃ N : ℕ, 1 ≤ N ∧ X / 2 ≤ (N : ℝ) ∧
      (N : ℝ) ≤ max 1 X ∧ (1 ≤ X → (N : ℝ) ≤ X) := by
  by_cases hXone : 1 ≤ X
  · let N : ℕ := ⌊X⌋₊
    have hN : 1 ≤ N := by
      dsimp [N]
      exact (Nat.one_le_floor_iff X).2 hXone
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast (show 0 < N by omega)
    have hfloor : (N : ℝ) ≤ X := by
      dsimp [N]
      exact Nat.floor_le hX.le
    have hXlt : X < (N : ℝ) + 1 := by
      dsimp [N]
      simpa [Nat.cast_add_one] using Nat.lt_floor_add_one X
    have hstep : (N : ℝ) + 1 ≤ 2 * N := by
      have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hhalf : X / 2 ≤ (N : ℝ) := by
      linarith [hXlt.le.trans hstep]
    exact ⟨N, hN, hhalf, hfloor.trans (le_max_right _ _), fun _ => hfloor⟩
  · have hXle : X ≤ 1 := le_of_not_ge hXone
    refine ⟨1, by simp, ?_, ?_, ?_⟩
    · norm_num
      linarith
    · simp [max_eq_left hXle]
    · exact fun h => (hXone h).elim

/- [derived consequence of paper lines 837--858 and `co:tail`, lines
1158--1169] This is `weighted_height_tsum_tail_inv_pow_le` with the
manuscript's positive real cutoff `X`.  Above one it uses the proved natural
tail with `N = floor X`; below one it uses absolute summability of the full
series.  Thus the single constant is selected before `X`, and no
cutoff-dependent constant is hidden. -/
set_option maxHeartbeats 1600000 in
theorem weighted_height_tsum_tail_real_inv_pow_le
    {alpha : Type*} {H : alpha → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hpq : p < q)
    {w : alpha → ℝ} {C : ℝ} (hC : 0 < C)
    (hw : ∀ x : alpha, 1 ≤ H x →
      |w x| ≤ C * (H x)⁻¹ ^ q) :
    ∃ Ctail : ℝ, 0 < Ctail ∧ ∀ {X : ℝ}, 0 < X →
      (∑' x : {x : alpha // X ≤ H x}, |w x.1|) ≤
        Ctail * X ^ (-((q - p : ℕ) : ℝ)) := by
  obtain ⟨Cnat, hCnat, htail⟩ :=
    weighted_height_tsum_tail_inv_pow_le hcount hpq hC hw
  have habs : Summable (fun x : alpha => |w x|) := by
    apply summable_of_abs_le_height_inv_pow_all hcount hpq
    intro x hx
    simpa only [abs_abs] using hw x hx
  let S : ℝ := ∑' x : alpha, |w x|
  have hS : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg fun _ => abs_nonneg _
  let r : ℕ := q - p
  have hr : 0 < r := by
    dsimp [r]
    exact Nat.sub_pos_of_lt hpq
  let Ctail : ℝ := Cnat * (2 : ℝ) ^ (r : ℝ) + S + 1
  have hlead : 0 < Cnat * (2 : ℝ) ^ (r : ℝ) := by positivity
  have hCtail : 0 < Ctail := by
    dsimp [Ctail]
    linarith
  refine ⟨Ctail, hCtail, ?_⟩
  intro X hX
  let betaX := {x : alpha // X ≤ H x}
  have hsumX : Summable (fun x : betaX => |w x.1|) := by
    exact habs.comp_injective Subtype.val_injective
  by_cases hXone : 1 ≤ X
  · let N : ℕ := ⌊X⌋₊
    have hN : 1 ≤ N := by
      dsimp [N]
      exact (Nat.one_le_floor_iff X).2 hXone
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast (show 0 < N by omega)
    have hfloor : (N : ℝ) ≤ X := by
      dsimp [N]
      exact Nat.floor_le hX.le
    have hXlt : X < (N : ℝ) + 1 := by
      dsimp [N]
      simpa [Nat.cast_add_one] using Nat.lt_floor_add_one X
    have hstep : (N : ℝ) + 1 ≤ 2 * N := by
      have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hhalf : X / 2 ≤ (N : ℝ) := by
      linarith [hXlt.le.trans hstep]
    let betaN := {x : alpha // (N : ℝ) ≤ H x}
    let e : betaX → betaN := fun x => ⟨x.1, hfloor.trans x.2⟩
    have he : Function.Injective e := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : betaN => z.1) hxy
    have hsumN : Summable (fun x : betaN => |w x.1|) := by
      exact habs.comp_injective Subtype.val_injective
    have hsubset :
        (∑' x : betaX, |w x.1|) ≤ ∑' x : betaN, |w x.1| := by
      exact hsumX.tsum_le_tsum_of_inj e he
        (fun x hx => abs_nonneg (w x.1)) (fun _ => le_rfl) hsumN
    have htailN :
        (∑' x : betaN, |w x.1|) ≤
          Cnat * (N : ℝ) ^ (-((r : ℕ) : ℝ)) := by
      simpa [betaN, r] using htail hN
    have hhalfpos : 0 < X / 2 := by positivity
    have hneg : -((r : ℕ) : ℝ) < 0 := by
      exact neg_lt_zero.mpr (by exact_mod_cast hr)
    have hmon :
        (N : ℝ) ^ (-((r : ℕ) : ℝ)) ≤
          (X / 2) ^ (-((r : ℕ) : ℝ)) := by
      exact (Real.rpow_le_rpow_iff_of_neg hNpos hhalfpos hneg).2 hhalf
    have hscale :
        (X / 2) ^ (-((r : ℕ) : ℝ)) =
          (2 : ℝ) ^ (r : ℝ) * X ^ (-((r : ℕ) : ℝ)) := by
      rw [Real.div_rpow hX.le (by positivity)]
      rw [Real.rpow_neg hX.le, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2)]
      simp only [div_eq_mul_inv, inv_inv]
      ring
    have hcoef : Cnat * (2 : ℝ) ^ (r : ℝ) ≤ Ctail := by
      dsimp [Ctail]
      linarith
    calc
      (∑' x : betaX, |w x.1|) ≤
          ∑' x : betaN, |w x.1| := hsubset
      _ ≤ Cnat * (N : ℝ) ^ (-((r : ℕ) : ℝ)) := htailN
      _ ≤ Cnat * ((X / 2) ^ (-((r : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hmon hCnat.le
      _ = (Cnat * (2 : ℝ) ^ (r : ℝ)) *
          X ^ (-((r : ℕ) : ℝ)) := by rw [hscale]; ring
      _ ≤ Ctail * X ^ (-((q - p : ℕ) : ℝ)) := by
        dsimp [r]
        exact mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hX.le _)
  · have hXle : X ≤ 1 := le_of_not_ge hXone
    have hsubset : (∑' x : betaX, |w x.1|) ≤ S := by
      dsimp [S]
      exact hsumX.tsum_le_tsum_of_inj (fun x : betaX => x.1)
        Subtype.val_injective (fun x hx => abs_nonneg (w x))
        (fun _ => le_rfl) habs
    have hpower : 1 ≤ X ^ (-((q - p : ℕ) : ℝ)) := by
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hX hXle
      exact neg_nonpos.mpr (Nat.cast_nonneg _)
    have hSC : S ≤ Ctail := by
      dsimp [Ctail]
      linarith
    calc
      (∑' x : betaX, |w x.1|) ≤ S := hsubset
      _ ≤ Ctail * 1 := by simpa using hSC
      _ ≤ Ctail * X ^ (-((q - p : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hpower hCtail.le

/- [Lean infrastructure] If every point outside `B` lies beyond the real
height cutoff `X`, absolute summability injects the complement series into
the corresponding height tail.  This is only the subtype bookkeeping behind
paper `co:tail`; it asserts no geometric estimate. -/
theorem tsum_complement_abs_le_height_tail
    {alpha : Type*} {H : alpha → ℝ} {g : alpha → ℝ}
    (habs : Summable (fun x : alpha => |g x|))
    (B : Set alpha) {X : ℝ}
    (houtside : ∀ x : alpha, x ∉ B → X ≤ H x) :
    |∑' x : {x : alpha // x ∉ B}, g x.1| ≤
      ∑' x : {x : alpha // X ≤ H x}, |g x.1| := by
  let beta := {x : alpha // x ∉ B}
  let betaX := {x : alpha // X ≤ H x}
  let e : beta → betaX := fun x => ⟨x.1, houtside x.1 x.2⟩
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : betaX => z.1) hxy
  have hsumBeta : Summable (fun x : beta => |g x.1|) := by
    exact habs.comp_injective Subtype.val_injective
  have hsumBetaX : Summable (fun x : betaX => |g x.1|) := by
    exact habs.comp_injective Subtype.val_injective
  have hsubset :
      (∑' x : beta, |g x.1|) ≤ ∑' x : betaX, |g x.1| := by
    exact hsumBeta.tsum_le_tsum_of_inj e he
      (fun x hx => abs_nonneg (g x.1)) (fun _ => le_rfl) hsumBetaX
  have hsumNorm : Summable (fun x : beta => ‖g x.1‖) := by
    simpa [Real.norm_eq_abs] using hsumBeta
  calc
    |∑' x : beta, g x.1| ≤ ∑' x : beta, |g x.1| := by
      simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsumNorm
    _ ≤ ∑' x : betaX, |g x.1| := hsubset

/- [Lean infrastructure for paper `co:tail`, lines 1158--1169] Exact bridge
between the reciprocal natural-power form produced by the real-cutoff proof
and the manuscript notation `T ^ (-d)`. -/
theorem inv_nat_pow_eq_zpow_neg_nat (T : ℝ) (d : ℕ) :
    (T ^ d)⁻¹ = T ^ (-(d : ℤ)) := by
  rw [zpow_neg, zpow_natCast]

/- [derived consequence of paper `le:lower_bound_not_in_F`, lines
1132--1155] This is the manuscript's echelon height lower bound with its
quantifiers exposed in the order used by `co:tail`: `C_lower` is chosen once,
before `T`.  The proof repeats the already proved ingredients of
`exists_uniform_echelon_height_lower_bound_of_not_mem_calF`, because that
older interface fixes `T` before returning the constant. -/
set_option maxHeartbeats 1600000 in
theorem exists_uniform_echelon_height_lower_bound_for_all_scales
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hkn : k ≤ n) (hkm : k ≤ m) (hk : 0 < k)
    {Csup Cprod : ℝ}
    (hCsup : 0 < Csup) (hCprod : 0 < Cprod)
    (hprod : ∀ D : EchelonMatrix K k m,
      (∏ i : Fin k,
        ‖((rowSuccessiveMinimum (echelonRowSpace D) i :
            rowZLattice (echelonRowSpace D)) :
            rowRealSpan (echelonRowSpace D))‖ ^ degree K) ≤
        Cprod * rowSpaceHeight (echelonRowSpace D)) :
    ∃ Clower : ℝ, 0 < Clower ∧ ∀ T : ℝ, 0 < T →
      ∀ D : EchelonMatrix K k m,
        D ∉ calF (K := K) (l := k) (m := m) (n := n) Csup T →
          Clower * T ^ degree K ≤ rowSpaceHeight (echelonRowSpace D) := by
  have hm : 0 < m := lt_of_lt_of_le hk hkm
  obtain ⟨delta, hdelta, hmin⟩ :=
    exists_uniform_integral_row_minimum_lower_bound_all (K := K) (m := m) hm
  let Ccut : ℝ := (k : ℝ) ^ (-1 / 2 : ℝ) * Csup
  have hCcut : 0 < Ccut := by
    dsimp [Ccut]
    positivity
  let Clower : ℝ := ((delta ^ (k - 1) * Ccut) ^ degree K) / Cprod
  have hClower : 0 < Clower := by
    dsimp [Clower]
    positivity
  refine ⟨Clower, hClower, ?_⟩
  intro T hT D hD
  let V : Grassmannian K m k := echelonRowSpace D
  have hminV : ∀ i : Fin k,
      delta ≤ ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ :=
    hmin V hkm hk
  have hlastNot : ¬
      ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ : rowZLattice V) :
          rowRealSpan V)‖ ≤ Ccut * T := by
    intro hle
    apply hD
    apply echelon_mem_calF_of_last_successiveMinimum_norm_le
      D hkn hk hCsup hT
    change ‖((rowSuccessiveMinimum (echelonRowSpace D) ⟨k - 1, by omega⟩ :
        rowZLattice (echelonRowSpace D)) :
        rowRealSpan (echelonRowSpace D))‖ ≤
      (k : ℝ) ^ (-1 / 2 : ℝ) * Csup * T at hle
    exact hle
  have hlast : Ccut * T ≤
      ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ : rowZLattice V) :
          rowRealSpan V)‖ := (lt_of_not_ge hlastNot).le
  have hd : 0 < degree K := Module.finrank_pos
  have hprodD := hprod D
  change (∏ i : Fin k,
      ‖((rowSuccessiveMinimum (echelonRowSpace D) i :
          rowZLattice (echelonRowSpace D)) :
          rowRealSpan (echelonRowSpace D))‖ ^ degree K) ≤
    Cprod * rowSpaceHeight (echelonRowSpace D) at hprodD
  have hbound := rowSpaceHeight_lower_bound_of_minima
    (V := V) (d := degree K) hd hk hdelta hCcut hCprod hT hminV hlast hprodD
  change (((delta ^ (k - 1) * Ccut) ^ degree K) / Cprod) *
    T ^ degree K ≤ rowSpaceHeight V
  exact hbound

/- [derived consequence of paper `eq:defi_of_calF`, lines 1073--1082, and
`le:lower_bound_not_in_F`, lines 1132--1155] The preceding uniform echelon
bound is transported through the proved exact equality between
`echelonRowSpace '' calF` and `boundedRowSpaces`.  This is the precise family
used by `MainTheorems`, not a support enlargement. -/
set_option maxHeartbeats 1600000 in
theorem exists_uniform_boundedRowSpaces_complement_height_lower_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hkn : k ≤ n) (hkm : k ≤ m) (hk : 0 < k)
    {Csup Cprod : ℝ}
    (hCsup : 0 < Csup) (hCprod : 0 < Cprod)
    (hprod : ∀ D : EchelonMatrix K k m,
      (∏ i : Fin k,
        ‖((rowSuccessiveMinimum (echelonRowSpace D) i :
            rowZLattice (echelonRowSpace D)) :
            rowRealSpan (echelonRowSpace D))‖ ^ degree K) ≤
        Cprod * rowSpaceHeight (echelonRowSpace D)) :
    ∃ Clower : ℝ, 0 < Clower ∧ ∀ T : ℝ, 0 < T →
      ∀ V : Grassmannian K m k,
        V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T →
          Clower * T ^ degree K ≤ rowSpaceHeight V := by
  obtain ⟨Clower, hClower, hheight⟩ :=
    exists_uniform_echelon_height_lower_bound_for_all_scales
      hkn hkm hk hCsup hCprod hprod
  refine ⟨Clower, hClower, ?_⟩
  intro T hT V hV
  let e := echelonRowSpaceEquiv (K := K) (l := k) (m := m)
  let D : EchelonMatrix K k m := e.symm V
  have hDV : echelonRowSpace D = V := e.apply_symm_apply V
  have hDnot : D ∉ calF (K := K) (l := k) (m := m) (n := n) Csup T := by
    intro hD
    apply hV
    have hmem : echelonRowSpace D ∈
        boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T :=
      echelon_calF_subset_boundedRowSpaces
        (K := K) (l := k) (m := m) (n := n) (Csup := Csup) (T := T)
        ⟨D, hD, rfl⟩
    rwa [hDV] at hmem
  have hheightD := hheight T hT D hDnot
  rwa [hDV] at hheightD

/- [derived consequence] The product hypothesis in the preceding theorem is
discharged by the proved Fieker--Stehlé/Minkowski-II product bound
`exists_rowSuccessiveMinimum_product_le_height_of_euclideanMinkowskiSecond`.
Its constant, like `C_lower`, is selected before `T`; no product estimate is
left as a hidden or scale-dependent assumption. -/
theorem exists_uniform_boundedRowSpaces_complement_height_lower_bound_of_fiekerStehle
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hkn : k ≤ n) (hkm : k ≤ m) (hk : 0 < k)
    {Csup : ℝ} (hCsup : 0 < Csup) :
    ∃ Clower : ℝ, 0 < Clower ∧ ∀ T : ℝ, 0 < T →
      ∀ V : Grassmannian K m k,
        V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T →
          Clower * T ^ degree K ≤ rowSpaceHeight V := by
  obtain ⟨Cprod, hCprod, hprod⟩ :=
    exists_rowSuccessiveMinimum_product_le_height_of_euclideanMinkowskiSecond
      (K := K) (m := m) (k := k) hk
  exact exists_uniform_boundedRowSpaces_complement_height_lower_bound
    hkn hkm hk hCsup hCprod (fun D => hprod (echelonRowSpace D))

/- [derived consequence of paper `co:tail`, lines 1158--1169, used in the
final assembly at lines 1641--1697, specifically `eq:nonrequired_eq` at
1653--1665] Uniform height-tail input for the exact `boundedRowSpaces` family.
The constants are chosen before `T`.  The proof first obtains the direct
Schmidt decay `T ^ (-degree K * (n-m))` and then uses `n-m ≥ 1` to return
exactly the manuscript's `T ^ (-degree K)` notation.  In the
degree-one, rank-one exceptional case of lines 1716--1724 it specializes to
an ordinary `T⁻¹` tail, which is absorbed by the manuscript's
`T⁻¹ * log T` scale via `inv_le_two_mul_inv_mul_log_of_two_le`.

The witness `X` is exactly the manuscript cutoff.  The natural `N` is within
a factor two below `X` and no larger than `max 1 X`; when `X ≥ 1`, it is
also a valid lower height cutoff for every omitted row space. -/
set_option maxHeartbeats 2400000 in
theorem exists_uniform_boundedRowSpaces_mainConstant_complement_tail
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
          ∃ N : ℕ, 1 ≤ N ∧ X / 2 ≤ (N : ℝ) ∧
            (N : ℝ) ≤ max 1 X ∧
            (∀ V : Grassmannian K m k,
              V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
                Csup T → X ≤ rowSpaceHeight V) ∧
            (1 ≤ X → ∀ V : Grassmannian K m k,
              V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
                Csup T → (N : ℝ) ≤ rowSpaceHeight V) ∧
            |∑' V : {V : Grassmannian K m k //
                V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
                Csup T},
              (rowMatrixLatticeCovolume V.1 n)⁻¹ *
                rowMatrixSubspaceIntegral V.1 n f| ≤
              Ctail * T ^ (-(degree K : ℤ)) := by
  obtain ⟨Clower, hClower, hheight⟩ :=
    exists_uniform_boundedRowSpaces_complement_height_lower_bound_of_fiekerStehle
      (K := K) (n := n) (m := m) (k := k) (Csup := Csup)
      hkn hkm hk hCsup
  let g : Grassmannian K m k → ℝ := fun V =>
    (rowMatrixLatticeCovolume V n)⁻¹ * rowMatrixSubspaceIntegral V n f
  have hgdom : ∀ V : Grassmannian K m k, 1 ≤ rowSpaceHeight V →
      |g V| ≤ C * (rowSpaceHeight V)⁻¹ ^ n := by
    intro V hV
    simpa [g, rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow, inv_pow] using
      hdom V hV
  obtain ⟨Creal, hCreal, hrealTail⟩ :=
    weighted_height_tsum_tail_real_inv_pow_le hcount hnm hC hgdom
  have habs : Summable (fun V : Grassmannian K m k => |g V|) := by
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
  obtain ⟨N, hN, hhalf, hNmax, hNbelow⟩ :=
    exists_nat_height_cutoff_below_comparable X hX
  have houtside : ∀ V : Grassmannian K m k,
      V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T →
        X ≤ rowSpaceHeight V := by
    intro V hV
    exact hheight T hT V hV
  have hNatOutside : 1 ≤ X → ∀ V : Grassmannian K m k,
      V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T →
        (N : ℝ) ≤ rowSpaceHeight V := by
    intro hXone V hV
    exact (hNbelow hXone).trans (houtside V hV)
  have hcompl :
      |∑' V : {V : Grassmannian K m k //
          V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
            Csup T}, g V.1| ≤
        ∑' V : {V : Grassmannian K m k // X ≤ rowSpaceHeight V},
          |g V.1| :=
    tsum_complement_abs_le_height_tail habs
      (boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T)
      houtside
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
  have hpow : T ^ degree K ≤ T ^ (degree K * (n - m)) := by
    exact pow_le_pow_right₀ (le_trans (by norm_num) hTtwo) hexponents
  have hdecay :
      (T ^ (degree K * (n - m)))⁻¹ ≤ T ^ (-(degree K : ℤ)) := by
    rw [← inv_nat_pow_eq_zpow_neg_nat T (degree K)]
    exact (inv_le_inv₀ (pow_pos hT _) (pow_pos hT _)).2 hpow
  refine ⟨X, rfl, hX, N, hN, hhalf, hNmax, houtside, hNatOutside, ?_⟩
  calc
    |∑' V : {V : Grassmannian K m k //
        V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
          Csup T},
        (rowMatrixLatticeCovolume V.1 n)⁻¹ *
          rowMatrixSubspaceIntegral V.1 n f| =
        |∑' V : {V : Grassmannian K m k //
          V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
            Csup T}, g V.1| := by rfl
    _ ≤ ∑' V : {V : Grassmannian K m k // X ≤ rowSpaceHeight V},
        |g V.1| := hcompl
    _ ≤ Creal * X ^ (-((n - m : ℕ) : ℝ)) := htailX
    _ = Ctail * (T ^ (degree K * (n - m)))⁻¹ := by
      rw [hscale]
      dsimp [Ctail]
      ring
    _ ≤ Ctail * T ^ (-(degree K : ℤ)) :=
      mul_le_mul_of_nonneg_left hdecay hCtail.le

/- [derived consequence of paper `co:tail`, lines 1158--1169, and the final
assembly `eq:nonrequired_eq`, lines 1653--1665 within lines 1641--1697]
Assembly-ready finite-family form of the preceding complement estimate.  The
identity is the absolutely summable decomposition of `mainConstant` into the
exact `boundedRowSpaces` subtype and its complement.  In particular,
`C_lower` and `C_tail` remain outside both the `T` and `Fintype` binders.

For the exceptional degree-one/rank-one assembly at lines 1716--1724, the
right side is literally `Ctail * T⁻¹`; the already proved theorem
`inv_le_two_mul_inv_mul_log_of_two_le` embeds it into `T⁻¹ log T`. -/
set_option maxHeartbeats 2400000 in
theorem exists_uniform_boundedRowSpaces_mainConstant_tail_abs_le
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
        ∀ [Fintype (boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
          Csup T)],
          |mainConstant n m k f -
              finiteRowMatrixMainTermSum
                (boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
                  Csup T) f| ≤
            Ctail * T ^ (-(degree K : ℤ)) := by
  obtain ⟨Clower, Ctail, hClower, hCtail, htail⟩ :=
    exists_uniform_boundedRowSpaces_mainConstant_complement_tail
      hnm hkn hkm hk hCsup hcount hC hdom
  refine ⟨Clower, Ctail, hClower, hCtail, ?_⟩
  intro T hTtwo inst
  obtain ⟨X, hX, hXpos, N, hN, hhalf, hNmax, houtside,
      hNoutside, hcompl⟩ := htail T hTtwo
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
  calc
    |mainConstant n m k f - finiteRowMatrixMainTermSum B f| =
        |∑' V : {V : Grassmannian K m k // V ∉ B}, g V.1| := by
      rw [hdecomp]
      simp
    _ ≤ Ctail * T ^ (-(degree K : ℤ)) := by
      simpa [B, g] using hcompl

end Katznelson
