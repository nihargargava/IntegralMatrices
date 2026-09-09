import Katznelson.Counting.Admissible
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Quantitative lattice Riemann sums

This file develops Lemma `le:Riemann_estimate` of `papers/katznelson.tex`.
For a full `ℤ`-lattice, we use the half-open fundamental parallelepiped of
an arbitrary lattice basis.  Its explicit radius plays the role of the
paper's covering radius in the cell-by-cell estimate.
-/

namespace Katznelson

open MeasureTheory Set Module
open scoped Classical MeasureTheory Pointwise

/- The top submodule has exactly the ambient metric. -/
noncomputable def topSubmoduleIsometryEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (⊤ : Submodule ℝ E) ≃ᵢ E where
  __ := Submodule.topEquiv.toEquiv
  isometry_toFun _ _ := rfl

@[simp]
theorem topSubmoduleIsometryEquiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : (⊤ : Submodule ℝ E)) :
    topSubmoduleIsometryEquiv x = (x : E) := rfl

section AdmissibleAmbient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [FiniteDimensional ℝ E] in
theorem Admissible.error_integrable_ambient {f : E → ℝ}
    (h_f : Admissible f) {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    Integrable (fun x : E => errorFunction f x ε)
      (μHE[Module.finrank ℝ E] : Measure E) := by
  let e := topSubmoduleIsometryEquiv (E := E)
  have htop := h_f.error_integrable (⊤ : Submodule ℝ E) top_ne_bot ε hε hεone
  have htop' : Integrable
      (fun x : (⊤ : Submodule ℝ E) => errorFunction f (x : E) ε)
      (μHE[Module.finrank ℝ (⊤ : Submodule ℝ E)] :
        Measure (⊤ : Submodule ℝ E)) :=
    (euclideanIntegrable_iff _).mp htop
  have hmp : MeasurePreserving e
      (μHE[Module.finrank ℝ (⊤ : Submodule ℝ E)] :
        Measure (⊤ : Submodule ℝ E))
      (μHE[Module.finrank ℝ (⊤ : Submodule ℝ E)] : Measure E) :=
    e.measurePreserving_euclideanHausdorffMeasure _
  have hcomp :
      (fun x : E => errorFunction f x ε) ∘ e =
        fun x : (⊤ : Submodule ℝ E) => errorFunction f (x : E) ε := by
    funext x
    rfl
  have hamb := (hmp.integrable_comp_emb
      e.toHomeomorph.toMeasurableEquiv.measurableEmbedding).mp (by
    rw [hcomp]
    exact htop')
  simpa using hamb

omit [FiniteDimensional ℝ E] in
theorem Admissible.exists_error_bound_ambient {f : E → ℝ}
    (h_f : Admissible f) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∫ x : E, errorFunction f x ε
        ∂(μHE[Module.finrank ℝ E] : Measure E) ≤ C * ε := by
  obtain ⟨C, hC, hbound⟩ := h_f.error_bound
  refine ⟨C, hC, fun ε hε hεone => ?_⟩
  let e := topSubmoduleIsometryEquiv (E := E)
  have htop := hbound (⊤ : Submodule ℝ E) top_ne_bot ε hε hεone
  rw [euclideanIntegral_eq_integral] at htop
  have hmp : MeasurePreserving e
      (μHE[Module.finrank ℝ (⊤ : Submodule ℝ E)] :
        Measure (⊤ : Submodule ℝ E))
      (μHE[Module.finrank ℝ (⊤ : Submodule ℝ E)] : Measure E) :=
    e.measurePreserving_euclideanHausdorffMeasure _
  have hint := hmp.integral_comp
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun x : E => errorFunction f x ε)
  have hdim : Module.finrank ℝ (⊤ : Submodule ℝ E) =
      Module.finrank ℝ E := by simp
  rw [← hdim]
  rw [← hint]
  have hefun :
      (fun x : (⊤ : Submodule ℝ E) => errorFunction f (e x) ε) =
        fun x : (⊤ : Submodule ℝ E) => errorFunction f (x : E) ε := by
    funext x
    rfl
  rw [hefun]
  simpa using htop

end AdmissibleAmbient

section FundamentalDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

abbrev LatticeBasisIndex := Module.Free.ChooseBasisIndex ℤ L

/- An arbitrary integral basis of `L`. -/
noncomputable def latticeBasis : Basis (LatticeBasisIndex L) ℤ L :=
  Module.Free.chooseBasis ℤ L

/- The same family as a real basis of the ambient span. -/
noncomputable def latticeRealBasis : Basis (LatticeBasisIndex L) ℝ E :=
  (latticeBasis L).ofZLatticeBasis ℝ

/- The half-open fundamental parallelepiped used in the proof. -/
noncomputable def latticeFundamentalDomain : Set E :=
  ZSpan.fundamentalDomain (latticeRealBasis L)

/- A uniform norm bound for that fundamental domain. -/
noncomputable def latticeFundamentalRadius : ℝ :=
  ∑ i, ‖latticeRealBasis L i‖

theorem latticeFundamentalRadius_nonneg :
    0 ≤ latticeFundamentalRadius L := by
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem latticeFundamentalRadius_pos [Nontrivial E] :
    0 < latticeFundamentalRadius L := by
  let i : LatticeBasisIndex L :=
    Classical.choice (latticeRealBasis L).index_nonempty
  have hi : 0 < ‖latticeRealBasis L i‖ :=
    norm_pos_iff.mpr ((latticeRealBasis L).ne_zero i)
  exact hi.trans_le (Finset.single_le_sum
    (fun j _ => norm_nonneg (latticeRealBasis L j)) (Finset.mem_univ i))

theorem norm_le_latticeFundamentalRadius {x : E}
    (hx : x ∈ latticeFundamentalDomain L) :
    ‖x‖ ≤ latticeFundamentalRadius L := by
  rw [← ZSpan.fract_eq_self.mpr hx]
  exact ZSpan.norm_fract_le (latticeRealBasis L) x

theorem latticeFundamentalDomain_isBounded :
    Bornology.IsBounded (latticeFundamentalDomain L) :=
  ZSpan.fundamentalDomain_isBounded (latticeRealBasis L)

theorem latticeFundamentalDomain_isAddFundamentalDomain
    [MeasurableSpace E] [OpensMeasurableSpace E] (mu : Measure E) :
    IsAddFundamentalDomain L (latticeFundamentalDomain L) mu := by
  exact ZLattice.isAddFundamentalDomain (latticeBasis L) mu

theorem lattice_ball_finite [ProperSpace E] {T : ℝ} :
    Set.Finite {v : L | ‖(v : E)‖ ≤ T} := by
  have hLclosed : IsClosed (L : Set E) :=
    @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
  have hfinite :
      Set.Finite (Metric.closedBall (0 : E) T ∩ (L : Set E)) :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall hLclosed
  refine (hfinite.preimage Subtype.val_injective.injOn).subset ?_
  intro v hv
  change (v : E) ∈ Metric.closedBall (0 : E) T ∩ (L : Set E)
  constructor
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact hv
  · exact v.2

theorem covolume_eq_measureReal_latticeFundamentalDomain
    [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) [Measure.IsAddHaarMeasure mu] :
    ZLattice.covolume L mu =
      mu.real (latticeFundamentalDomain L) := by
  exact ZLattice.covolume_eq_measure_fundamentalDomain L mu
    (latticeFundamentalDomain_isAddFundamentalDomain L mu)

/- The paper's Lemma `le:ballvol` (lines 463--478).  The proof below uses
the explicit half-open fundamental domain already used for the Riemann-sum
estimate; its radius is a valid covering-radius substitute for this coarse
bound. -/
theorem lattice_ball_count
    [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    (mu : Measure E) [Measure.IsAddHaarMeasure mu] {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧
      (Set.ncard {v : L | ‖(v : E)‖ ≤ T} : ℝ) ≤
        C * (T + latticeFundamentalRadius L) ^ Module.finrank ℝ E *
          (ZLattice.covolume L mu)⁻¹ := by
  let S : Set L := {v : L | ‖(v : E)‖ ≤ T}
  let F : Set E := latticeFundamentalDomain L
  let R : ℝ := latticeFundamentalRadius L
  have hS : S.Finite := by
    simpa [S] using lattice_ball_finite L
  have hR : 0 ≤ R := latticeFundamentalRadius_nonneg L
  have hTR : 0 ≤ T + R := by linarith
  have hFtop : mu F ≠ ⊤ :=
    ne_of_lt (latticeFundamentalDomain_isBounded L).measure_lt_top
  have hfund : IsAddFundamentalDomain L F mu :=
    latticeFundamentalDomain_isAddFundamentalDomain L mu
  have hunion :
      (⋃ v ∈ hS.toFinset, (v : E) +ᵥ F) ⊆
        Metric.closedBall (0 : E) (T + R) := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨v, hv, hx⟩
    have hvS : v ∈ S := hS.mem_toFinset.mp hv
    rcases Set.mem_vadd_set.mp hx with ⟨y, hy, hxy⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [← hxy, vadd_eq_add]
    calc
      ‖(v : E) + y‖ ≤ ‖(v : E)‖ + ‖y‖ := norm_add_le _ _
      _ ≤ T + R := add_le_add hvS (norm_le_latticeFundamentalRadius L hy)
  have hmeasure :
      mu.real (⋃ v ∈ hS.toFinset, (v : E) +ᵥ F) =
        (hS.toFinset.card : ℝ) * mu.real F := by
    rw [measureReal_biUnion_finset₀
      (hd := by
        intro v hv w hw hvw
        exact hfund.aedisjoint hvw)
      (hm := by
        intro v hv
        exact hfund.nullMeasurableSet.vadd (v : E))
      (h := by
        intro v hv
        rw [MeasureTheory.measure_vadd mu (v : E)]
        exact hFtop)]
    simp [MeasureTheory.measureReal_def, MeasureTheory.measure_vadd]
  have hmeasure_le :
      (hS.toFinset.card : ℝ) * mu.real F ≤
        (T + R) ^ Module.finrank ℝ E *
          mu.real (Metric.closedBall (0 : E) 1) := by
    rw [← hmeasure]
    calc
      mu.real (⋃ v ∈ hS.toFinset, (v : E) +ᵥ F) ≤
          mu.real (Metric.closedBall (0 : E) (T + R)) :=
        measureReal_mono hunion measure_closedBall_lt_top.ne
      _ = (T + R) ^ Module.finrank ℝ E *
          mu.real (Metric.closedBall (0 : E) 1) :=
        MeasureTheory.Measure.addHaar_real_closedBall' mu 0 hTR
  have hcard :
      (Set.ncard S : ℝ) * ZLattice.covolume L mu ≤
        (T + R) ^ Module.finrank ℝ E *
          mu.real (Metric.closedBall (0 : E) 1) := by
    rw [Set.ncard_eq_toFinset_card S hS,
      covolume_eq_measureReal_latticeFundamentalDomain L mu]
    exact hmeasure_le
  have hcovpos : 0 < ZLattice.covolume L mu := ZLattice.covolume_pos L mu
  have hunitpos : 0 < mu.real (Metric.closedBall (0 : E) 1) := by
    rw [MeasureTheory.measureReal_def]
    apply ENNReal.toReal_pos
    · exact (Metric.measure_closedBall_pos mu 0 zero_lt_one).ne'
    · exact measure_closedBall_lt_top.ne
  refine ⟨mu.real (Metric.closedBall (0 : E) 1), hunitpos, ?_⟩
  have hdiv :
      (Set.ncard S : ℝ) ≤
        ((T + R) ^ Module.finrank ℝ E *
          mu.real (Metric.closedBall (0 : E) 1)) /
          ZLattice.covolume L mu :=
    (le_div_iff₀ hcovpos).2 hcard
  simpa [S, R, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

end FundamentalDomain

section FiniteSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ProperSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

omit [FiniteDimensional ℝ E] [IsZLattice ℝ L] in
theorem finite_scaledSupport_lattice_of_hasCompactSupport (f : E → ℝ)
    (hcompact : HasCompactSupport f)
    {T : ℝ} (hT : 0 < T) :
    Set.Finite {v : L | f (T⁻¹ • (v : E)) ≠ 0} := by
  obtain ⟨R, hsupport⟩ := hcompact.isBounded.subset_closedBall (0 : E)
  have hLclosed : IsClosed (L : Set E) :=
    @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
  have hfinite :
      Set.Finite (Metric.closedBall (0 : E) (R * T) ∩ (L : Set E)) :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall hLclosed
  refine (hfinite.preimage Subtype.val_injective.injOn).subset ?_
  intro v hv
  change (v : E) ∈ Metric.closedBall (0 : E) (R * T) ∩ (L : Set E)
  constructor
  · have hvSupport : T⁻¹ • (v : E) ∈ tsupport f :=
      subset_closure (show T⁻¹ • (v : E) ∈ Function.support f from hv)
    have hvBall := hsupport hvSupport
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos hT] at hvBall
    have hTne : T ≠ 0 := hT.ne'
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖(v : E)‖ = T * (T⁻¹ * ‖(v : E)‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hTne, one_mul]
      _ ≤ T * R := mul_le_mul_of_nonneg_left hvBall hT.le
      _ = R * T := mul_comm _ _
  · exact v.2

omit [FiniteDimensional ℝ E] [IsZLattice ℝ L] in
theorem finite_scaledSupport_lattice (f : E → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    Set.Finite {v : L | f (T⁻¹ • (v : E)) ≠ 0} :=
  finite_scaledSupport_lattice_of_hasCompactSupport L f h_f.compactSupport hT

omit [FiniteDimensional ℝ E] [IsZLattice ℝ L] in
theorem summable_scaled_lattice_of_hasCompactSupport (f : E → ℝ)
    (hcompact : HasCompactSupport f) {T : ℝ} (hT : 0 < T) :
    Summable (fun v : L => f (T⁻¹ • (v : E))) := by
  exact summable_of_hasFiniteSupport
    (finite_scaledSupport_lattice_of_hasCompactSupport L f hcompact hT)

omit [FiniteDimensional ℝ E] [IsZLattice ℝ L] in
theorem summable_scaled_lattice (f : E → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    Summable (fun v : L => f (T⁻¹ • (v : E))) := by
  exact summable_scaled_lattice_of_hasCompactSupport L f h_f.compactSupport hT

end FiniteSupport

section FilteredFiniteSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ProperSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/- A compactly supported scaled function has a finite rank-filtered lattice
   sum.  This is the counting estimate used for the inner sum in the
   lower-rank induction argument. -/
theorem lattice_subtype_scaled_sum_abs_le
    (P : L → Prop) (g : E → ℝ) (hcompact : HasCompactSupport g)
    {T B C : ℝ} (hT : 0 < T)
    (hsupport : ∀ v : L, g (T⁻¹ • (v : E)) ≠ 0 → ‖(v : E)‖ ≤ B)
    (hbound : ∀ v : L, |g (T⁻¹ • (v : E))| ≤ C) (hC : 0 ≤ C) :
    |∑' v : {v : L // P v}, g (T⁻¹ • (v.1 : E))| ≤
      C * (Set.ncard {v : L | ‖(v : E)‖ ≤ B} : ℝ) := by
  let u : {v : L // P v} → ℝ := fun v => g (T⁻¹ • (v.1 : E))
  let uf : L → ℝ := fun v => g (T⁻¹ • (v : E))
  have hUf : (Function.support uf).Finite := by
    change Set.Finite {v : L | uf v ≠ 0}
    simpa [uf] using
      finite_scaledSupport_lattice_of_hasCompactSupport L g hcompact hT
  have hU : (Function.support u).Finite := by
    change Set.Finite {v : {v : L // P v} | u v ≠ 0}
    refine (hUf.preimage Subtype.val_injective.injOn).subset ?_
    intro v hv
    exact hv
  let hball : Set.Finite {v : L | ‖(v : E)‖ ≤ B} :=
    lattice_ball_finite L
  have hsum : ∑' v : {v : L // P v}, u v =
      ∑ v ∈ hU.toFinset, u v := by
    apply tsum_eq_sum
    intro v hv
    change u v = 0
    by_contra hzero
    apply hv
    exact hU.mem_toFinset.mpr hzero
  have hcard : hU.toFinset.card ≤
      (Set.ncard {v : L | ‖(v : E)‖ ≤ B}) := by
    have himage : (Subtype.val '' Function.support u).Finite :=
      hU.image Subtype.val
    have hsubset : Subtype.val '' Function.support u ⊆
        {v : L | ‖(v : E)‖ ≤ B} := by
      rintro v ⟨w, hw, rfl⟩
      exact hsupport w hw
    calc
      hU.toFinset.card = Set.ncard (Function.support u) := by
        rw [Set.ncard_eq_toFinset_card (Function.support u) hU]
      _ = Set.ncard (Subtype.val '' Function.support u) := by
        symm
        exact Set.ncard_image_of_injective _ Subtype.val_injective
      _ ≤ Set.ncard {v : L | ‖(v : E)‖ ≤ B} :=
        Set.ncard_le_ncard hsubset hball
  rw [hsum]
  calc
    |∑ v ∈ hU.toFinset, u v| ≤
        ∑ v ∈ hU.toFinset, |u v| := by
      simpa using Finset.abs_sum_le_sum_abs (fun v => u v) hU.toFinset
    _ ≤ ∑ v ∈ hU.toFinset, C := by
      apply Finset.sum_le_sum
      intro v hv
      exact hbound v.1
    _ = hU.toFinset.card * C := by
      simp
    _ ≤ (Set.ncard {v : L | ‖(v : E)‖ ≤ B} : ℝ) * C := by
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hC
    _ = C * (Set.ncard {v : L | ‖(v : E)‖ ≤ B} : ℝ) := by
      ring

end FilteredFiniteSupport

section ScaledOscillation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem Admissible.scaled_error_integrable {f : E → ℝ}
    (h_f : Admissible f) {T ε : ℝ} (hT : 0 < T)
    (hε : 0 < ε) (hεone : ε ≤ 1) :
    Integrable (fun x : E => errorFunction f (T⁻¹ • x) ε)
      (μHE[Module.finrank ℝ E] : Measure E) := by
  exact (h_f.error_integrable_ambient hε hεone).comp_smul
    (inv_ne_zero hT.ne')

omit [Nontrivial E] in
theorem integral_scaled (g : E → ℝ) {T : ℝ}
    (hT : 0 ≤ T) :
    (∫ x : E, g (T⁻¹ • x)
        ∂(μHE[Module.finrank ℝ E] : Measure E)) =
      T ^ Module.finrank ℝ E *
        ∫ x : E, g x
          ∂(μHE[Module.finrank ℝ E] : Measure E) := by
  simpa [smul_eq_mul] using
    (Measure.integral_comp_inv_smul_of_nonneg
      (μHE[Module.finrank ℝ E] : Measure E)
      g hT)

omit [Nontrivial E] in
theorem integral_scaled_error {f : E → ℝ} {T ε : ℝ}
    (hT : 0 ≤ T) :
    (∫ x : E, errorFunction f (T⁻¹ • x) ε
        ∂(μHE[Module.finrank ℝ E] : Measure E)) =
      T ^ Module.finrank ℝ E *
        ∫ x : E, errorFunction f x ε
          ∂(μHE[Module.finrank ℝ E] : Measure E) :=
  integral_scaled (fun x : E => errorFunction f x ε) hT

end ScaledOscillation

section CellEstimate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

theorem dist_scaled_add_latticePoint_le {T : ℝ} (hT : 0 < T)
    (v : L) {x : E} (hx : x ∈ latticeFundamentalDomain L) :
    dist (T⁻¹ • ((v : E) + x)) (T⁻¹ • (v : E)) ≤
      latticeFundamentalRadius L / T := by
  have hxnorm := norm_le_latticeFundamentalRadius L hx
  have hTinv : 0 ≤ T⁻¹ := inv_nonneg.mpr hT.le
  calc
    dist (T⁻¹ • ((v : E) + x)) (T⁻¹ • (v : E)) =
        T⁻¹ * ‖x‖ := by
      rw [dist_eq_norm, ← smul_sub, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hTinv]
    _ ≤ T⁻¹ * latticeFundamentalRadius L :=
      mul_le_mul_of_nonneg_left hxnorm hTinv
    _ = latticeFundamentalRadius L / T := by
      rw [div_eq_mul_inv, mul_comm]

variable [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [Nontrivial E] in
theorem integral_vadd_latticeFundamentalDomain (g : E → ℝ) (v : L) :
    ∫ x in v +ᵥ latticeFundamentalDomain L, g x
        ∂(μHE[Module.finrank ℝ E] : Measure E) =
      ∫ x in latticeFundamentalDomain L, g ((v : E) + x)
        ∂(μHE[Module.finrank ℝ E] : Measure E) := by
  let mu : Measure E := (μHE[Module.finrank ℝ E] : Measure E)
  have hmp := measurePreserving_add_left mu (v : E)
  have hemb :=
    (Homeomorph.addLeft (v : E)).toMeasurableEquiv.measurableEmbedding
  have hset : v +ᵥ latticeFundamentalDomain L =
      (v : E) +ᵥ latticeFundamentalDomain L := by
    ext x
    rfl
  rw [hset, ← Set.image_vadd]
  simpa only [vadd_eq_add, mu] using hmp.setIntegral_image_emb hemb g
    (latticeFundamentalDomain L)

omit [Nontrivial E] in
theorem summable_integral_latticeFundamentalDomain (g : E → ℝ)
    (hg : Integrable g
      (μHE[Module.finrank ℝ E] : Measure E)) :
    Summable (fun v : L =>
      ∫ x in latticeFundamentalDomain L, g ((v : E) + x)
        ∂(μHE[Module.finrank ℝ E] : Measure E)) := by
  let mu : Measure E := (μHE[Module.finrank ℝ E] : Measure E)
  let F : Set E := latticeFundamentalDomain L
  let _ : VAddInvariantMeasure L E mu :=
    ⟨fun v s _ => by
      change mu ((fun x : E => (v : E) + x) ⁻¹' s) = mu s
      exact measure_preimage_add mu (v : E) s⟩
  have hfund : IsAddFundamentalDomain L F mu :=
    latticeFundamentalDomain_isAddFundamentalDomain L mu
  have hsumIntegrable : Integrable g
      (Measure.sum fun v : L => mu.restrict (v +ᵥ F)) := by
    rw [hfund.sum_restrict]
    exact hg
  have hnormCells : Summable (fun v : L =>
      ∫ x in F, ‖g ((v : E) + x)‖ ∂mu) := by
    refine hsumIntegrable.summable_integral.congr (fun v => ?_)
    change (∫ x in v +ᵥ F, ‖g x‖ ∂mu) =
      ∫ x in F, ‖g ((v : E) + x)‖ ∂mu
    exact integral_vadd_latticeFundamentalDomain L (fun x => ‖g x‖) v
  apply Summable.of_norm
  exact hnormCells.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun v => norm_integral_le_integral_norm
      (fun x => g ((v : E) + x)))

theorem cell_integral_error_bound (f : E → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) (v : L)
    (hRadius : latticeFundamentalRadius L / T ≤ 1) :
    |∫ x in latticeFundamentalDomain L,
        (f (T⁻¹ • (v : E)) - f (T⁻¹ • ((v : E) + x)))
        ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
      ∫ x in latticeFundamentalDomain L,
        errorFunction f (T⁻¹ • ((v : E) + x))
          (latticeFundamentalRadius L / T)
        ∂(μHE[Module.finrank ℝ E] : Measure E) := by
  let mu : Measure E :=
    (μHE[Module.finrank ℝ E] : Measure E)
  let ε := latticeFundamentalRadius L / T
  have hε : 0 < ε := by
    exact div_pos (latticeFundamentalRadius_pos L) hT
  have hbase : Integrable
      (fun x : E => errorFunction f (T⁻¹ • x) ε) mu := by
    exact h_f.scaled_error_integrable hT hε hRadius
  have htranslated : Integrable
      (fun x : E => errorFunction f (T⁻¹ • ((v : E) + x)) ε) mu := by
    have hmp := measurePreserving_add_left mu (v : E)
    simpa [Function.comp_def] using hmp.integrable_comp_of_integrable hbase
  have hF : MeasurableSet (latticeFundamentalDomain L) :=
    ZSpan.fundamentalDomain_measurableSet (latticeRealBasis L)
  rw [← Real.norm_eq_abs]
  change ‖∫ x in latticeFundamentalDomain L,
      (f (T⁻¹ • (v : E)) - f (T⁻¹ • ((v : E) + x))) ∂mu‖ ≤
    ∫ x in latticeFundamentalDomain L,
      errorFunction f (T⁻¹ • ((v : E) + x)) ε ∂mu
  apply norm_integral_le_of_norm_le htranslated.restrict
  filter_upwards [ae_restrict_mem hF] with x hx
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact h_f.abs_sub_le_errorFunction
    (dist_scaled_add_latticePoint_le L hT v hx)

/- Summing the cellwise errors is legitimate because the translated
fundamental domains decompose Haar measure.  This is the quantitative core
of Lemma `le:Riemann_estimate`, lines 582--607 of the paper. -/
theorem tsum_cell_integral_error_bound (f : E → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T)
    (hRadius : latticeFundamentalRadius L / T ≤ 1) :
    |∑' v : L, ∫ x in latticeFundamentalDomain L,
        (f (T⁻¹ • (v : E)) - f (T⁻¹ • ((v : E) + x)))
        ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
      ∫ x : E, errorFunction f (T⁻¹ • x)
        (latticeFundamentalRadius L / T)
        ∂(μHE[Module.finrank ℝ E] : Measure E) := by
  let mu : Measure E := (μHE[Module.finrank ℝ E] : Measure E)
  let _ : VAddInvariantMeasure L E mu :=
    ⟨fun v s _ => by
      change mu ((fun x : E => (v : E) + x) ⁻¹' s) = mu s
      exact measure_preimage_add mu (v : E) s⟩
  let F : Set E := latticeFundamentalDomain L
  let ε : ℝ := latticeFundamentalRadius L / T
  let g : E → ℝ := fun x => errorFunction f (T⁻¹ • x) ε
  let a : L → ℝ := fun v =>
    ∫ x in F, f (T⁻¹ • (v : E)) - f (T⁻¹ • ((v : E) + x)) ∂mu
  let b : L → ℝ := fun v => ∫ x in F, g ((v : E) + x) ∂mu
  have hε : 0 < ε := div_pos (latticeFundamentalRadius_pos L) hT
  have hbase : Integrable g mu := by
    exact h_f.scaled_error_integrable hT hε hRadius
  have hfund : IsAddFundamentalDomain L F mu := by
    exact latticeFundamentalDomain_isAddFundamentalDomain L mu
  have hsumIntegrable : Integrable g
      (Measure.sum fun v : L => mu.restrict (v +ᵥ F)) := by
    rw [hfund.sum_restrict]
    exact hbase
  have hnormg : (fun x : E => ‖g x‖) = g := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact h_f.errorFunction_nonneg hε.le
  have hb : Summable b := by
    have hb' := hsumIntegrable.summable_integral
    refine hb'.congr (fun v => ?_)
    change (∫ x in v +ᵥ F, ‖g x‖ ∂mu) = b v
    rw [hnormg]
    exact integral_vadd_latticeFundamentalDomain L g v
  have hba : ∀ v, ‖a v‖ ≤ b v := by
    intro v
    dsimp only [a, b, g, F, ε, mu]
    rw [Real.norm_eq_abs]
    exact cell_integral_error_bound L f h_f hT v hRadius
  have haNorm : Summable (fun v => ‖a v‖) :=
    hb.of_nonneg_of_le (fun v => norm_nonneg (a v)) hba
  have hb_tsum : ∑' v, b v = ∫ x : E, g x ∂mu := by
    calc
      ∑' v, b v = ∑' v : L, ∫ x in F, g (v +ᵥ x) ∂mu := by
        apply tsum_congr
        intro v
        rfl
      _ = ∫ x : E, g x ∂mu :=
        (hfund.integral_eq_tsum'' g hbase).symm
  change |∑' v, a v| ≤ ∫ x : E, g x ∂mu
  rw [← Real.norm_eq_abs]
  calc
    ‖∑' v, a v‖ ≤ ∑' v, ‖a v‖ := norm_tsum_le_tsum_norm haNorm
    _ ≤ ∑' v, b v := haNorm.tsum_le_tsum hba hb
    _ = ∫ x : E, g x ∂mu := hb_tsum

/- The cell sum is exactly the covolume-weighted lattice sum minus the
scaled ambient integral. -/
theorem covolume_mul_latticeSum_sub_integral_le (f : E → ℝ)
    (h_f : Admissible f) {T : ℝ} (hT : 0 < T)
    (hRadius : latticeFundamentalRadius L / T ≤ 1) :
    |ZLattice.covolume L
          (μHE[Module.finrank ℝ E] : Measure E) *
        (∑' v : L, f (T⁻¹ • (v : E))) -
        ∫ x : E, f (T⁻¹ • x)
          ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
      ∫ x : E, errorFunction f (T⁻¹ • x)
        (latticeFundamentalRadius L / T)
        ∂(μHE[Module.finrank ℝ E] : Measure E) := by
  let mu : Measure E := (μHE[Module.finrank ℝ E] : Measure E)
  let F : Set E := latticeFundamentalDomain L
  let C : ℝ := ZLattice.covolume L mu
  let scaled : E → ℝ := fun x => f (T⁻¹ • x)
  let cellIntegral : L → ℝ := fun v =>
    ∫ x in F, scaled ((v : E) + x) ∂mu
  let cellError : L → ℝ := fun v =>
    ∫ x in F, scaled (v : E) - scaled ((v : E) + x) ∂mu
  let _ : VAddInvariantMeasure L E mu :=
    ⟨fun v s _ => by
      change mu ((fun x : E => (v : E) + x) ⁻¹' s) = mu s
      exact measure_preimage_add mu (v : E) s⟩
  have hfIntegrable : Integrable f mu := by
    exact (euclideanIntegrable_iff f).mp h_f.integrable
  have hscaled : Integrable scaled mu := by
    exact hfIntegrable.comp_smul (inv_ne_zero hT.ne')
  have hlattice : Summable (fun v : L => scaled (v : E)) := by
    exact summable_scaled_lattice L f h_f hT
  have hcells : Summable cellIntegral := by
    exact summable_integral_latticeFundamentalDomain L scaled hscaled
  have hFfinite : mu F ≠ ⊤ := by
    exact ne_of_lt (latticeFundamentalDomain_isBounded L).measure_lt_top
  have hcellError (v : L) :
      cellError v = C * scaled (v : E) - cellIntegral v := by
    have htranslated : Integrable (fun x : E => scaled ((v : E) + x)) mu := by
      have hmp := measurePreserving_add_left mu (v : E)
      simpa [Function.comp_def] using hmp.integrable_comp_of_integrable hscaled
    have hconst : IntegrableOn (fun _ : E => scaled (v : E)) F mu :=
      integrableOn_const hFfinite
    dsimp only [cellError, cellIntegral]
    rw [integral_sub hconst htranslated.restrict,
      setIntegral_const, smul_eq_mul]
    change mu.real F * scaled (v : E) -
        (∫ x in F, scaled ((v : E) + x) ∂mu) =
      C * scaled (v : E) -
        ∫ x in F, scaled ((v : E) + x) ∂mu
    rw [← covolume_eq_measureReal_latticeFundamentalDomain L mu]
  have hfund : IsAddFundamentalDomain L F mu :=
    latticeFundamentalDomain_isAddFundamentalDomain L mu
  have hintegral : ∫ x : E, scaled x ∂mu = ∑' v, cellIntegral v := by
    rw [hfund.integral_eq_tsum'' scaled hscaled]
    apply tsum_congr
    intro v
    apply integral_congr_ae
    filter_upwards with x
    rfl
  have hidentity :
      C * (∑' v : L, scaled (v : E)) - ∫ x : E, scaled x ∂mu =
        ∑' v, cellError v := by
    calc
      C * (∑' v : L, scaled (v : E)) - ∫ x : E, scaled x ∂mu =
          (∑' v : L, C * scaled (v : E)) - ∑' v, cellIntegral v := by
        rw [tsum_mul_left, hintegral]
      _ = ∑' v : L, (C * scaled (v : E) - cellIntegral v) :=
        ((hlattice.mul_left C).tsum_sub hcells).symm
      _ = ∑' v, cellError v := by
        apply tsum_congr
        intro v
        exact (hcellError v).symm
  change |C * (∑' v : L, scaled (v : E)) -
      ∫ x : E, scaled x ∂mu| ≤
    ∫ x : E, errorFunction f (T⁻¹ • x)
      (latticeFundamentalRadius L / T) ∂mu
  rw [hidentity]
  exact tsum_cell_integral_error_bound L f h_f hT hRadius

/- Lemma `le:Riemann_estimate` in the paper, first in the equivalent form
with the covolume kept on the lattice-sum side. -/
theorem latticeRiemann_estimate_weighted (f : E → ℝ)
    (h_f : Admissible f) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      latticeFundamentalRadius L / T ≤ 1 →
      |ZLattice.covolume L
            (μHE[Module.finrank ℝ E] : Measure E) *
          ((∑' v : L, f (T⁻¹ • (v : E))) /
            T ^ Module.finrank ℝ E) -
          ∫ x : E, f x
            ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
        Cₐ * latticeFundamentalRadius L / T := by
  obtain ⟨Cₐ, hCₐ, herror⟩ := h_f.exists_error_bound_ambient
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  let q : ℕ := Module.finrank ℝ E
  let scale : ℝ := T ^ q
  let covol : ℝ := ZLattice.covolume L
    (μHE[Module.finrank ℝ E] : Measure E)
  let latticeSum : ℝ := ∑' v : L, f (T⁻¹ • (v : E))
  let ambientIntegral : ℝ :=
    ∫ x : E, f x ∂(μHE[Module.finrank ℝ E] : Measure E)
  let ε : ℝ := latticeFundamentalRadius L / T
  have hε : 0 < ε := div_pos (latticeFundamentalRadius_pos L) hT
  have hscale : 0 < scale := pow_pos hT q
  have hraw := covolume_mul_latticeSum_sub_integral_le
    L f h_f hT hRadius
  change |covol * latticeSum -
      ∫ x : E, f (T⁻¹ • x)
        ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
    ∫ x : E, errorFunction f (T⁻¹ • x) ε
      ∂(μHE[Module.finrank ℝ E] : Measure E) at hraw
  rw [integral_scaled f hT.le, integral_scaled_error hT.le] at hraw
  change |covol * latticeSum - scale * ambientIntegral| ≤
      scale * ∫ x : E, errorFunction f x ε
        ∂(μHE[Module.finrank ℝ E] : Measure E) at hraw
  have herrorε := herror ε hε hRadius
  have hraw' : |covol * latticeSum - scale * ambientIntegral| ≤
      scale * (Cₐ * ε) :=
    hraw.trans (mul_le_mul_of_nonneg_left herrorε hscale.le)
  have hidentity :
      covol * (latticeSum / scale) - ambientIntegral =
        (covol * latticeSum - scale * ambientIntegral) / scale := by
    field_simp [hscale.ne']
  change |covol * (latticeSum / scale) - ambientIntegral| ≤
    Cₐ * latticeFundamentalRadius L / T
  rw [hidentity, abs_div, abs_of_pos hscale]
  apply (div_le_iff₀ hscale).2
  simpa [ε, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hraw'

/- The normalized form appearing on line 574 of `papers/katznelson.tex`.
Our explicit fundamental-domain radius replaces the Voronoi covering radius;
the proof is otherwise the paper's argument verbatim. -/
theorem latticeRiemann_estimate (f : E → ℝ) (h_f : Admissible f) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      latticeFundamentalRadius L / T ≤ 1 →
      |(∑' v : L, f (T⁻¹ • (v : E))) /
            T ^ Module.finrank ℝ E -
          (ZLattice.covolume L
            (μHE[Module.finrank ℝ E] : Measure E))⁻¹ *
            ∫ x : E, f x
              ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
        Cₐ * latticeFundamentalRadius L /
          (ZLattice.covolume L
            (μHE[Module.finrank ℝ E] : Measure E) * T) := by
  obtain ⟨Cₐ, hCₐ, hweighted⟩ := latticeRiemann_estimate_weighted L f h_f
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  let covol : ℝ := ZLattice.covolume L
    (μHE[Module.finrank ℝ E] : Measure E)
  let latticeAverage : ℝ :=
    (∑' v : L, f (T⁻¹ • (v : E))) / T ^ Module.finrank ℝ E
  let ambientIntegral : ℝ :=
    ∫ x : E, f x ∂(μHE[Module.finrank ℝ E] : Measure E)
  have hcovol : 0 < covol := by
    exact ZLattice.covolume_pos L
      (μHE[Module.finrank ℝ E] : Measure E)
  have hbound := hweighted T hT hRadius
  change |covol * latticeAverage - ambientIntegral| ≤
    Cₐ * latticeFundamentalRadius L / T at hbound
  have hidentity :
      latticeAverage - covol⁻¹ * ambientIntegral =
        (covol * latticeAverage - ambientIntegral) / covol := by
    field_simp [hcovol.ne']
  have hrhs :
      Cₐ * latticeFundamentalRadius L / (covol * T) =
        (Cₐ * latticeFundamentalRadius L / T) / covol := by
    field_simp [hcovol.ne', hT.ne']
  change |latticeAverage - covol⁻¹ * ambientIntegral| ≤
    Cₐ * latticeFundamentalRadius L / (covol * T)
  rw [hidentity, abs_div, abs_of_pos hcovol, hrhs]
  exact (div_le_div_iff_of_pos_right hcovol).2 hbound

end CellEstimate

end Katznelson
