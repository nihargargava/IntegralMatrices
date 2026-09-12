import Katznelson.Counting.Admissible
import Katznelson.Lattice
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.InnerProductSpace.Affine
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
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

/- [Lean infrastructure] The Euclidean unit-ball volume, written explicitly
   as a function of the real dimension.  This is used only to retain the
   uniformity of the implicit ball-count constant when the lattice lives in a
   varying subspace of fixed dimension. -/
noncomputable def euclideanUnitBallVolume (q : ℕ) : ℝ :=
  Real.sqrt Real.pi ^ q / Real.Gamma ((q : ℝ) / 2 + 1)

/- [Lean infrastructure] Positivity of the dimension-only Euclidean
   unit-ball volume. -/
theorem euclideanUnitBallVolume_pos (q : ℕ) :
    0 < euclideanUnitBallVolume q := by
  unfold euclideanUnitBallVolume
  apply div_pos
  · exact pow_pos (Real.sqrt_pos.2 Real.pi_pos) _
  · apply Real.Gamma_pos_of_pos
    positivity

/- [Lean infrastructure] The Euclidean Hausdorff measure of a unit ball is
   the preceding dimension-only constant.  This is a Mathlib volume formula,
   not an additional geometric input to the manuscript. -/
theorem euclideanHausdorffMeasureReal_unitClosedBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] :
    (μHE[Module.finrank ℝ E] : Measure E).real
        (Metric.closedBall (0 : E) 1) =
      euclideanUnitBallVolume (Module.finrank ℝ E) := by
  have hnonneg : 0 ≤ euclideanUnitBallVolume (Module.finrank ℝ E) :=
    (euclideanUnitBallVolume_pos _).le
  have hvolume : volume (Metric.closedBall (0 : E) 1) =
      ENNReal.ofReal (euclideanUnitBallVolume (Module.finrank ℝ E)) := by
    rw [InnerProductSpace.volume_closedBall]
    simp [euclideanUnitBallVolume]
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
    MeasureTheory.measureReal_def, hvolume]
  exact ENNReal.toReal_ofReal hnonneg

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

/- [paper, lines 431--445] The Voronoi domain used in the manuscript.  The
   lattice is viewed inside its real span, so the translated point is written
   using the subtype coercion from `L`. -/
noncomputable def latticeVoronoiDomain : Set E :=
  {x | ∀ v : L, ‖x‖ ≤ ‖x + (v : E)‖}

/- [paper, equation (the definition at lines 433--437)] Zero belongs to the
   Voronoi domain. -/
theorem zero_mem_latticeVoronoiDomain :
    (0 : E) ∈ latticeVoronoiDomain L := by
  intro v
  simp [latticeVoronoiDomain]

/- [derived consequence, paper lines 441--444] If a lattice point is a
   nearest point to `x`, translating `x` by that point produces a point of the
   Voronoi domain. -/
theorem sub_mem_latticeVoronoiDomain_of_isNearest
    {x : E} {v : L}
    (hmin : ∀ w : L, dist x (v : E) ≤ dist x (w : E)) :
    x - (v : E) ∈ latticeVoronoiDomain L := by
  intro u
  have h := hmin (v - u)
  rw [dist_eq_norm, dist_eq_norm] at h
  have harg : x - ((v - u : L) : E) =
      (x - (v : E)) + (u : E) := by
    change x - ((v : E) - (u : E)) = (x - (v : E)) + (u : E)
    abel
  change ‖x - (v : E)‖ ≤ ‖(x - (v : E)) + (u : E)‖
  rw [← harg]
  exact h

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

/- [derived consequence, paper `le:voronoi`, lines 447--457] The Voronoi
   domain is contained in a bounded fundamental-domain radius.  A point of a
   fixed parallelepiped is used only as a bound; it is not identified with the
   manuscript's intrinsic covering radius. -/
theorem norm_le_latticeFundamentalRadius_of_mem_latticeVoronoiDomain
    {x : E} (hx : x ∈ latticeVoronoiDomain L) :
    ‖x‖ ≤ latticeFundamentalRadius L := by
  let b := latticeRealBasis L
  have hb : Submodule.span ℤ (Set.range b) = L := by
    simpa [b, latticeRealBasis] using
      (latticeBasis L).ofZLatticeBasis_span ℝ
  obtain ⟨v₀, hv₀, _⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b x
  have hv₀mem : v₀.1 ∈ L := by
    simpa only [hb] using v₀.2
  let v : L := ⟨v₀.1, hv₀mem⟩
  have hvco : v.1 = v₀.1 := by
    rfl
  have hv : v +ᵥ x ∈ latticeFundamentalDomain L := by
    change v.1 + x ∈ ZSpan.fundamentalDomain b
    rw [hvco]
    change v₀.1 + x ∈ ZSpan.fundamentalDomain b at hv₀
    exact hv₀
  have hbound : ‖x + v.1‖ ≤ latticeFundamentalRadius L := by
    have hbound' := norm_le_latticeFundamentalRadius L hv
    change ‖v.1 + x‖ ≤ latticeFundamentalRadius L at hbound'
    simpa [add_comm] using hbound'
  exact (hx v).trans hbound

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

/- [derived consequence, paper lines 433--437] A full lattice has a nearest
   point to every ambient point.  The proof uses the finite lattice ball
   estimate above: a minimizer among a sufficiently large finite ball also
   minimizes globally by the triangle inequality. -/
theorem exists_lattice_nearest_point [ProperSpace E] (x : E) :
    ∃ v : L, ∀ w : L, dist x (v : E) ≤ dist x (w : E) := by
  let S : Set L := {v | ‖(v : E)‖ ≤ 2 * ‖x‖}
  have hSfinite : S.Finite := by
    simpa [S] using (lattice_ball_finite L (T := 2 * ‖x‖))
  have hSnonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    simp [S]
  obtain ⟨v, hvS, hmin⟩ := Set.exists_min_image S (fun w : L => dist x (w : E))
    hSfinite hSnonempty
  refine ⟨v, fun w => ?_⟩
  by_cases hwS : w ∈ S
  · exact hmin w hwS
  · have hwlarge : 2 * ‖x‖ < ‖(w : E)‖ := by
      exact lt_of_not_ge (by simpa [S] using hwS)
    have hv0 : dist x (v : E) ≤ dist x (0 : L) := by
      apply hmin 0
      simp [S]
    have hdist0 : dist x (0 : L) = ‖x‖ := by
      simp [dist_eq_norm]
    have hwbound : ‖(w : E)‖ ≤ dist x (w : E) + ‖x‖ := by
      calc
        ‖(w : E)‖ = ‖((w : E) - x) + x‖ := by
          congr 1
          abel
        _ ≤ ‖(w : E) - x‖ + ‖x‖ := norm_add_le _ _
        _ = dist x (w : E) + ‖x‖ := by
          rw [dist_eq_norm, norm_sub_rev]
    have hxlt : ‖x‖ < dist x (w : E) := by
      rw [← sub_pos] at hwlarge
      have := sub_le_iff_le_add.mpr hwbound
      linarith
    rw [hdist0] at hv0
    exact hv0.trans (le_of_lt hxlt)

/- [Lean infrastructure] The minimum distance to a lattice point, written as
   an `sInf` so that the paper's `min` can be related to standard order
   operations in Lean. -/
noncomputable def latticeNearestDistance (L : Submodule ℤ E) (x : E) : ℝ :=
  sInf ((fun v : L => dist x (v : E)) '' Set.univ)

/- [derived consequence, paper definition at lines 433--437] The order-
   theoretic minimum above is attained by an actual lattice point. -/
theorem latticeNearestDistance_eq_dist_nearest [ProperSpace E] (x : E) :
    ∃ v : L, (∀ w : L, dist x (v : E) ≤ dist x (w : E)) ∧
      latticeNearestDistance L x = dist x (v : E) := by
  obtain ⟨v, hmin⟩ := exists_lattice_nearest_point L x
  have hbelow : BddBelow ((fun w : L => dist x (w : E)) '' Set.univ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, -, rfl⟩
    exact dist_nonneg
  have hmem : dist x (v : E) ∈
      (fun w : L => dist x (w : E)) '' Set.univ :=
    ⟨v, Set.mem_univ _, rfl⟩
  have hleft : latticeNearestDistance L x ≤ dist x (v : E) := by
    exact csInf_le hbelow hmem
  have hright : dist x (v : E) ≤ latticeNearestDistance L x := by
    change dist x (v : E) ≤ sInf ((fun w : L => dist x (w : E)) '' Set.univ)
    apply le_csInf (Set.nonempty_of_mem hmem)
    rintro _ ⟨w, -, rfl⟩
    exact hmin w
  exact ⟨v, hmin, le_antisymm hleft hright⟩

/- [derived consequence, paper `le:voronoi`, lines 447--457] The norms of the
   Voronoi domain are bounded above by the radius of the fixed fundamental
   parallelepiped. -/
theorem bddAbove_norm_image_latticeVoronoiDomain :
    BddAbove ((fun x : E => ‖x‖) '' latticeVoronoiDomain L) := by
  refine ⟨latticeFundamentalRadius L, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact norm_le_latticeFundamentalRadius_of_mem_latticeVoronoiDomain L hx

/- [Lean infrastructure] Order-theoretic encoding of the numerical radius
   represented by the bounded Voronoi domain.  The following lemmas show that
   it supplies the covering property used in the manuscript; the equality
   with the paper's displayed `max min` expression is kept as a separate
   normalization bridge. -/
noncomputable def latticeCoveringRadius (L : Submodule ℤ E) : ℝ :=
  sSup ((fun x : E => ‖x‖) '' latticeVoronoiDomain L)

theorem latticeCoveringRadius_nonneg :
    0 ≤ latticeCoveringRadius L := by
  have hzero : (0 : ℝ) ∈ (fun x : E => ‖x‖) '' latticeVoronoiDomain L := by
    refine ⟨0, zero_mem_latticeVoronoiDomain L, norm_zero⟩
  simpa [latticeCoveringRadius] using
    (le_csSup (bddAbove_norm_image_latticeVoronoiDomain L) hzero)

theorem norm_le_latticeCoveringRadius_of_mem_latticeVoronoiDomain
    {x : E} (hx : x ∈ latticeVoronoiDomain L) :
    ‖x‖ ≤ latticeCoveringRadius L := by
  apply le_csSup (bddAbove_norm_image_latticeVoronoiDomain L)
  exact ⟨x, hx, rfl⟩

/- [derived consequence, paper `le:voronoi`, lines 447--457] The intrinsic
   Voronoi radius is no larger than the auxiliary radius of the chosen
   fundamental parallelepiped. -/
theorem latticeCoveringRadius_le_latticeFundamentalRadius :
    latticeCoveringRadius L ≤ latticeFundamentalRadius L := by
  apply csSup_le
  · exact ⟨0, ⟨0, zero_mem_latticeVoronoiDomain L, norm_zero⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact norm_le_latticeFundamentalRadius_of_mem_latticeVoronoiDomain L hx

/- [Lean infrastructure, paper definition at lines 433--437] The displayed
   `max min` radius is first represented by a supremum.  The following
   lemmas identify this representation with the Voronoi supremum; proving
   that the supremum is attained is a separate compactness statement. -/
noncomputable def latticeMaxMinRadius (L : Submodule ℤ E) : ℝ :=
  sSup ((fun x : E => latticeNearestDistance L x) '' Set.univ)

theorem latticeNearestDistance_nonneg (x : E) :
    0 ≤ latticeNearestDistance L x := by
  obtain ⟨v, _, hv⟩ := latticeNearestDistance_eq_dist_nearest L x
  rw [hv]
  exact dist_nonneg

theorem latticeNearestDistance_le_latticeFundamentalRadius (x : E) :
    latticeNearestDistance L x ≤ latticeFundamentalRadius L := by
  obtain ⟨v, hmin, hv⟩ := latticeNearestDistance_eq_dist_nearest L x
  rw [hv]
  rw [dist_eq_norm]
  exact norm_le_latticeFundamentalRadius_of_mem_latticeVoronoiDomain L
    (sub_mem_latticeVoronoiDomain_of_isNearest L hmin)

theorem bddAbove_latticeNearestDistance_image :
    BddAbove ((fun x : E => latticeNearestDistance L x) '' Set.univ) := by
  refine ⟨latticeFundamentalRadius L, ?_⟩
  rintro _ ⟨x, -, rfl⟩
  exact latticeNearestDistance_le_latticeFundamentalRadius L x

theorem latticeNearestDistance_zero :
    latticeNearestDistance L 0 = 0 := by
  obtain ⟨v, hmin, hv⟩ := latticeNearestDistance_eq_dist_nearest L 0
  rw [hv]
  apply le_antisymm
  · simpa [dist_eq_norm] using hmin (0 : L)
  · exact dist_nonneg

theorem nonempty_latticeNearestDistance_image :
    ((fun x : E => latticeNearestDistance L x) '' Set.univ).Nonempty := by
  refine ⟨0, ⟨0, Set.mem_univ _, latticeNearestDistance_zero L⟩⟩

theorem nonempty_latticeVoronoi_norm_image :
    ((fun x : E => ‖x‖) '' latticeVoronoiDomain L).Nonempty := by
  exact ⟨0, ⟨0, zero_mem_latticeVoronoiDomain L, norm_zero⟩⟩

theorem latticeNearestDistance_mem_latticeVoronoi_norm_image (x : E) :
    latticeNearestDistance L x ∈
      (fun y : E => ‖y‖) '' latticeVoronoiDomain L := by
  obtain ⟨v, hmin, hv⟩ := latticeNearestDistance_eq_dist_nearest L x
  refine ⟨x - (v : E),
    sub_mem_latticeVoronoiDomain_of_isNearest L hmin, ?_⟩
  simpa [dist_eq_norm] using hv.symm

theorem latticeVoronoi_norm_mem_latticeNearestDistance_image
    {x : E} (hx : x ∈ latticeVoronoiDomain L) :
    ‖x‖ ∈ (fun y : E => latticeNearestDistance L y) '' Set.univ := by
  have hmin0 : ∀ v : L, dist x (0 : L) ≤ dist x (v : E) := by
    intro v
    simpa [dist_eq_norm, sub_eq_add_neg] using hx (-v)
  obtain ⟨v, hmin, hv⟩ := latticeNearestDistance_eq_dist_nearest L x
  have hdist : dist x (v : E) = dist x (0 : L) :=
    le_antisymm (hmin (0 : L)) (hmin0 v)
  refine ⟨x, Set.mem_univ _, ?_⟩
  change latticeNearestDistance L x = ‖x‖
  rw [hv, hdist]
  simp [dist_eq_norm]

theorem latticeNearestDistance_eq_norm_of_mem_latticeVoronoiDomain
    {x : E} (hx : x ∈ latticeVoronoiDomain L) :
    latticeNearestDistance L x = ‖x‖ := by
  obtain ⟨v, hmin, hv⟩ := latticeNearestDistance_eq_dist_nearest L x
  have hmin0 : ∀ w : L, dist x (0 : L) ≤ dist x (w : E) := by
    intro w
    simpa [dist_eq_norm, sub_eq_add_neg] using hx (-w)
  have hdist : dist x (v : E) = dist x (0 : L) :=
    le_antisymm (hmin (0 : L)) (hmin0 v)
  rw [hv, hdist]
  simp [dist_eq_norm]

theorem latticeCoveringRadius_eq_latticeMaxMinRadius :
    latticeCoveringRadius L = latticeMaxMinRadius L := by
  apply le_antisymm
  · apply csSup_le (nonempty_latticeVoronoi_norm_image L)
    rintro r ⟨x, hx, rfl⟩
    apply le_csSup (bddAbove_latticeNearestDistance_image L)
    exact latticeVoronoi_norm_mem_latticeNearestDistance_image L hx
  · apply csSup_le (nonempty_latticeNearestDistance_image L)
    rintro r ⟨x, -, rfl⟩
    apply le_csSup (bddAbove_norm_image_latticeVoronoiDomain L)
    exact latticeNearestDistance_mem_latticeVoronoi_norm_image L x

/- [derived consequence, paper definition at lines 433--437] A nontrivial
   full lattice has strictly positive intrinsic covering radius.  Discreteness
   gives a ball about zero containing no nonzero lattice point; a point at
   half that radius has positive distance from every lattice point. -/
theorem latticeCoveringRadius_pos [ProperSpace E] [Nontrivial E] :
    0 < latticeCoveringRadius L := by
  obtain ⟨U, hUopen, hU⟩ :=
    (discreteTopology_subtype_iff'.mp (inferInstance : DiscreteTopology (L : Set E)))
      0 L.zero_mem
  have hzeroU : (0 : E) ∈ U := by
    have hzero : (0 : E) ∈ U ∩ (L : Set E) := by
      rw [hU]
      simp
    exact hzero.1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen 0 hzeroU
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  let x : E := (ε / (2 * ‖e‖)) • e
  have hepos : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hxnorm : ‖x‖ = ε / 2 := by
    dsimp [x]
    rw [norm_smul, Real.norm_of_nonneg]
    · field_simp
    · positivity
  have houtside : ∀ v : L, v ≠ 0 → ε ≤ ‖(v : E)‖ := by
    intro v hv
    by_contra hnot
    have hvball : (v : E) ∈ Metric.ball 0 ε := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_not_ge hnot
    have hvU := hball hvball
    have hvmem : (v : E) ∈ U ∩ (L : Set E) := ⟨hvU, v.property⟩
    rw [hU] at hvmem
    apply hv
    simpa using hvmem
  have hdist : ∀ v : L, ε / 2 ≤ dist x (v : E) := by
    intro v
    by_cases hv : v = 0
    · subst v
      simpa [dist_eq_norm, hxnorm]
    · rw [dist_eq_norm]
      have htri : ‖(v : E)‖ ≤ ‖(v : E) - x‖ + ‖x‖ := by
        calc
          ‖(v : E)‖ = ‖((v : E) - x) + x‖ := by
            congr 1
            abel
          _ ≤ ‖(v : E) - x‖ + ‖x‖ := norm_add_le _ _
      calc
        ε / 2 ≤ ‖(v : E)‖ - ‖x‖ := by rw [hxnorm]; linarith [houtside v hv]
        _ ≤ ‖(v : E) - x‖ := by linarith
        _ = ‖x - (v : E)‖ := norm_sub_rev _ _
  have hnearest : ε / 2 ≤ latticeNearestDistance L x := by
    obtain ⟨v, _, hv⟩ := latticeNearestDistance_eq_dist_nearest L x
    rw [hv]
    exact hdist v
  have hmax : ε / 2 ≤ latticeMaxMinRadius L := by
    exact hnearest.trans (le_csSup (bddAbove_latticeNearestDistance_image L)
      ⟨x, Set.mem_univ _, rfl⟩)
  rw [latticeCoveringRadius_eq_latticeMaxMinRadius L]
  exact lt_of_lt_of_le (half_pos hε) hmax

/- [derived consequence, paper `le:voronoi`, lines 447--457] The Voronoi
   domain is closed, since it is an intersection of closed norm inequalities. -/
theorem isClosed_latticeVoronoiDomain :
    IsClosed (latticeVoronoiDomain L) := by
  rw [show latticeVoronoiDomain L =
      ⋂ v : L, {x : E | ‖x‖ ≤ ‖x + (v : E)‖} by
    ext x
    simp [latticeVoronoiDomain]]
  exact isClosed_iInter fun v => isClosed_le continuous_norm (by fun_prop)

/- [derived consequence, paper `le:voronoi`, lines 447--457] Boundedness of
   the Voronoi domain together with closedness gives compactness in the proper
   finite-dimensional ambient space. -/
theorem isCompact_latticeVoronoiDomain [ProperSpace E] :
    IsCompact (latticeVoronoiDomain L) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_latticeVoronoiDomain L
  · rw [Metric.isBounded_iff_subset_closedBall (0 : E)]
    refine ⟨latticeFundamentalRadius L, ?_⟩
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_latticeFundamentalRadius_of_mem_latticeVoronoiDomain L hx

/- [derived consequence, paper definition at lines 433--437] Compactness
   supplies the `max` appearing in the manuscript's definition of `ρ`. -/
theorem exists_latticeCoveringRadius_max [ProperSpace E] :
    ∃ x : E, x ∈ latticeVoronoiDomain L ∧
      ‖x‖ = latticeCoveringRadius L := by
  have hcompact := isCompact_latticeVoronoiDomain L
  have hcont : ContinuousOn (fun x : E => ‖x‖) (latticeVoronoiDomain L) :=
    continuous_norm.continuousOn
  obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn
    ⟨0, zero_mem_latticeVoronoiDomain L⟩ hcont
  refine ⟨x, hx, ?_⟩
  apply le_antisymm
  · exact le_csSup (bddAbove_norm_image_latticeVoronoiDomain L)
      ⟨x, hx, rfl⟩
  · apply csSup_le (nonempty_latticeVoronoi_norm_image L)
    rintro r ⟨y, hy, rfl⟩
    exact hmax hy

/- [derived consequence, paper definition at lines 433--437] The maximum of
   the minimum-distance function is attained, matching the manuscript's
   `max` rather than only its order-theoretic supremum. -/
theorem exists_latticeMaxMinRadius_max [ProperSpace E] :
    ∃ x : E, latticeNearestDistance L x = latticeMaxMinRadius L := by
  obtain ⟨x, hx, hxr⟩ := exists_latticeCoveringRadius_max L
  refine ⟨x, ?_⟩
  calc
    latticeNearestDistance L x = ‖x‖ :=
      latticeNearestDistance_eq_norm_of_mem_latticeVoronoiDomain L hx
    _ = latticeCoveringRadius L := hxr
    _ = latticeMaxMinRadius L := latticeCoveringRadius_eq_latticeMaxMinRadius L

/- [derived consequence, paper lines 433--457] The Voronoi radius covers the
   whole real span: subtracting a nearest lattice point lands in the
   Voronoi domain and hence has norm at most the radius. -/
theorem latticeCovering_latticeCoveringRadius :
    LatticeCovering L (latticeCoveringRadius L) := by
  intro x
  obtain ⟨v, hmin⟩ := exists_lattice_nearest_point L x
  refine ⟨v, ?_⟩
  have hvor : x - (v : E) ∈ latticeVoronoiDomain L :=
    sub_mem_latticeVoronoiDomain_of_isNearest L hmin
  have hnorm := norm_le_latticeCoveringRadius_of_mem_latticeVoronoiDomain L hvor
  simpa [dist_eq_norm] using hnorm

/- [paper, the standard Voronoi fact used in `le:voronoi`, lines 447--457]
   In an inner-product space, the overlap of a Voronoi cell with a nontrivial
   lattice translate lies in the perpendicular bisector of that translate. -/
/- Any explicit covering estimate bounds the intrinsic Voronoi radius. -/
theorem latticeCoveringRadius_le_of_latticeCovering
    {R : ℝ} (hcover : LatticeCovering L R) :
    latticeCoveringRadius L ≤ R := by
  apply csSup_le (nonempty_latticeVoronoi_norm_image L)
  rintro r ⟨x, hx, rfl⟩
  obtain ⟨v, hv⟩ := hcover x
  obtain ⟨w, hwmin, hw⟩ := latticeNearestDistance_eq_dist_nearest L x
  have hnearest : latticeNearestDistance L x ≤ dist x (v : E) := by
    rw [hw]
    exact hwmin v
  have hnorm : ‖x‖ = latticeNearestDistance L x :=
    (latticeNearestDistance_eq_norm_of_mem_latticeVoronoiDomain L hx).symm
  calc
    ‖x‖ = latticeNearestDistance L x := hnorm
    _ ≤ dist x (v : E) := hnearest
    _ ≤ R := hv

/- A sublattice covering estimate is also an estimate for the ambient
   lattice.  This is the finite-index-free monotonicity used in the
   manuscript when replacing the ambient lattice by the lattice generated by
   its minima. -/
theorem latticeCovering_mono
    {L' : Submodule ℤ E} {R : ℝ} (hsub : L' ≤ L)
    (hcover : LatticeCovering L' R) :
    LatticeCovering L R := by
  intro x
  obtain ⟨v, hv⟩ := hcover x
  refine ⟨⟨v, hsub v.property⟩, ?_⟩
  simpa using hv

theorem latticeCoveringRadius_le_of_submodule
    {L' : Submodule ℤ E} {R : ℝ} (hsub : L' ≤ L)
    (hcover : LatticeCovering L' R) :
    latticeCoveringRadius L ≤ R :=
  latticeCoveringRadius_le_of_latticeCovering (L := L)
    (latticeCovering_mono (L := L) hsub hcover)

/- A finite real basis whose vectors lie in a lattice gives a covering bound
   for that lattice.  The proof uses the fundamental domain of the sublattice
   generated by the basis; this is the abstract form of the parallelepiped
   argument used in the manuscript's proof of part 2 of le:props_of_minima. -/
theorem latticeCovering_of_real_basis
    {ι : Type*} [Fintype ι]
    (b : Basis ι ℝ E) (L : Submodule ℤ E)
    (hmem : ∀ i, b i ∈ L) :
    LatticeCovering L (∑ i, ‖b i‖) := by
  intro x
  obtain ⟨v, hv, _⟩ :=
    ZSpan.exist_unique_vadd_mem_fundamentalDomain b x
  have hvL : (v : E) ∈ L := by
    apply Submodule.span_induction
      (p := fun y _ => y ∈ L) ?_ ?_ ?_ ?_ v.property
    · rintro y ⟨i, rfl⟩
      exact hmem i
    · exact L.zero_mem
    · intro y z _ _ hy hz
      exact L.add_mem hy hz
    · intro c y _ hy
      exact L.smul_mem c hy
  refine ⟨⟨-(v : E), L.neg_mem hvL⟩, ?_⟩
  rw [dist_eq_norm, sub_neg_eq_add]
  have hfract : ZSpan.fract b x = (v : E) + x := by
    calc
      ZSpan.fract b x = ZSpan.fract b ((v : E) + x) := by
        symm
        exact ZSpan.fract_zSpan_add b x v.property
      _ = (v : E) + x := ZSpan.fract_eq_self.mpr hv
  calc
    ‖x + (v : E)‖ = ‖(v : E) + x‖ := by rw [add_comm]
    _ = ‖ZSpan.fract b x‖ := by rw [hfract]
    _ ≤ ∑ i, ‖b i‖ := ZSpan.norm_fract_le b x

theorem latticeCoveringRadius_le_sum_of_real_basis
    {ι : Type*} [Fintype ι]
    (b : Basis ι ℝ E) (hmem : ∀ i, b i ∈ L) :
    latticeCoveringRadius L ≤ ∑ i, ‖b i‖ :=
  latticeCoveringRadius_le_of_latticeCovering (L := L)
    (latticeCovering_of_real_basis b L hmem)

noncomputable def latticeVoronoiBisector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) : AffineSubspace ℝ E :=
  AffineSubspace.mk' ((1 / 2 : ℝ) • v) (innerSL ℝ v).toLinearMap.ker

theorem latticeVoronoiBisector_ne_top
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v : E} (hv : v ≠ 0) : latticeVoronoiBisector v ≠ ⊤ := by
  intro htop
  have hker : (innerSL ℝ v).toLinearMap.ker = ⊤ := by
    have hdir := congrArg AffineSubspace.direction htop
    simpa [latticeVoronoiBisector] using hdir
  have hzero : (innerSL ℝ v).toLinearMap = 0 :=
    LinearMap.ker_eq_top.mp hker
  have hself : (innerSL ℝ v).toLinearMap v = 0 := by
    rw [hzero]
    simp
  have hpos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  change inner ℝ v v = 0 at hself
  rw [real_inner_self_eq_norm_sq] at hself
  linarith

theorem latticeVoronoi_mem_bisector_of_norm_eq_norm_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x v : E} (h : ‖x‖ = ‖x - v‖) :
    x ∈ latticeVoronoiBisector v := by
  rw [latticeVoronoiBisector, AffineSubspace.mem_mk']
  change (innerSL ℝ v).toLinearMap (x - (1 / 2 : ℝ) • v) = 0
  rw [map_sub, map_smul]
  change inner ℝ v x - (1 / 2 : ℝ) * inner ℝ v v = 0
  have hsq : ‖x - v‖ ^ 2 = ‖x‖ ^ 2 :=
    congrArg (fun r : ℝ => r ^ 2) h.symm
  have hnorm := norm_sub_sq_real x v
  have hi : inner ℝ x v = ‖v‖ ^ 2 / 2 := by
    linarith
  rw [real_inner_comm] at hi
  rw [real_inner_self_eq_norm_sq]
  linarith

theorem latticeVoronoi_inter_subset_bisector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    (v : L) (hv : (v : E) ≠ 0) :
    ((v : E) +ᵥ latticeVoronoiDomain L) ∩ latticeVoronoiDomain L ⊆
      (latticeVoronoiBisector (v : E) : Set E) := by
  intro x hx
  rcases (Set.mem_vadd_set.mp hx.1) with ⟨y, hy, hvadd⟩
  have hvadd' : y + (v : E) = x := by
    simpa [vadd_eq_add, add_comm] using hvadd
  have hxy : x - (v : E) = y := by
    rw [← hvadd]
    simp [vadd_eq_add]
  have hleft : ‖x - (v : E)‖ ≤ ‖x‖ := by
    rw [hxy]
    have h := hy v
    rw [hvadd'] at h
    exact h
  have hright : ‖x‖ ≤ ‖x - (v : E)‖ := by
    simpa [sub_eq_add_neg, vadd_eq_add] using hx.2 (-v)
  exact latticeVoronoi_mem_bisector_of_norm_eq_norm_sub
    (h := le_antisymm hright hleft)

/- The Voronoi cell is a fundamental domain for the lattice action.  This
   proves the measure-theoretic content of the paper's standard Voronoi fact:
   nearest-point existence gives coverage, while the bisector argument gives
   pairwise a.e. disjointness. -/
theorem latticeVoronoiDomain_isAddFundamentalDomain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (mu : Measure E) [Measure.IsAddHaarMeasure mu] :
    IsAddFundamentalDomain L (latticeVoronoiDomain L) mu := by
  have hmeas : NullMeasurableSet (latticeVoronoiDomain L) mu :=
    (isClosed_latticeVoronoiDomain L).nullMeasurableSet
  have hcover : ∀ x : E, ∃ g : L, g +ᵥ x ∈ latticeVoronoiDomain L := by
    intro x
    obtain ⟨v, hv⟩ := exists_lattice_nearest_point L x
    refine ⟨-v, ?_⟩
    convert sub_mem_latticeVoronoiDomain_of_isNearest L hv using 1
    change -(v : E) + x = x - (v : E)
    abel
  have hdisjoint : ∀ v : L, v ≠ 0 →
      AEDisjoint mu (v +ᵥ latticeVoronoiDomain L) (latticeVoronoiDomain L) := by
    intro v hv
    have hv' : (v : E) ≠ 0 := by
      intro h
      apply hv
      exact Subtype.ext h
    rw [AEDisjoint]
    change mu (((v : E) +ᵥ latticeVoronoiDomain L) ∩
      latticeVoronoiDomain L) = 0
    exact measure_mono_null
      (latticeVoronoi_inter_subset_bisector L v hv')
      (Measure.addHaar_affineSubspace mu (latticeVoronoiBisector (v : E))
        (latticeVoronoiBisector_ne_top hv'))
  have hqmp : ∀ v : L,
      Measure.QuasiMeasurePreserving (fun x : E => v +ᵥ x) mu mu := by
    intro v
    have hfun : (fun x : E => v +ᵥ x) = (fun x : E => (v : E) + x) := by
      funext x
      rfl
    rw [hfun]
    exact (measurePreserving_add_left mu (v : E)).quasiMeasurePreserving
  exact IsAddFundamentalDomain.mk'' hmeas
    (Filter.Eventually.of_forall hcover) hdisjoint hqmp

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
theorem lattice_ball_count_uniform
    [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    (mu : Measure E) [Measure.IsAddHaarMeasure mu] :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, 0 < T →
      (Set.ncard {v : L | ‖(v : E)‖ ≤ T} : ℝ) ≤
        C * (T + latticeFundamentalRadius L) ^ Module.finrank ℝ E *
          (ZLattice.covolume L mu)⁻¹ := by
  have hunitpos : 0 < mu.real (Metric.closedBall (0 : E) 1) := by
    rw [MeasureTheory.measureReal_def]
    apply ENNReal.toReal_pos
    · exact (Metric.measure_closedBall_pos mu 0 zero_lt_one).ne'
    · exact measure_closedBall_lt_top.ne
  refine ⟨mu.real (Metric.closedBall (0 : E) 1), hunitpos, ?_⟩
  intro T hT
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
  have hdiv :
      (Set.ncard S : ℝ) ≤
        ((T + R) ^ Module.finrank ℝ E *
          mu.real (Metric.closedBall (0 : E) 1)) /
          ZLattice.covolume L mu :=
    (le_div_iff₀ hcovpos).2 hcard
  simpa [S, R, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

/- [Lean infrastructure] Uniform-in-radius form of the preceding lattice
   ball count.  The constant is the fixed unit-ball volume from the proof,
   so it may be used in the ordinary-shell summation of
   `le:domain_dimension_bound`. -/
theorem lattice_ball_count
    [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    (mu : Measure E) [Measure.IsAddHaarMeasure mu] {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧
      (Set.ncard {v : L | ‖(v : E)‖ ≤ T} : ℝ) ≤
        C * (T + latticeFundamentalRadius L) ^ Module.finrank ℝ E *
          (ZLattice.covolume L mu)⁻¹ := by
  obtain ⟨C, hC, hcount⟩ := lattice_ball_count_uniform (L := L) mu
  exact ⟨C, hC, hcount hT⟩

end FundamentalDomain

/- [Lean infrastructure] Orthogonal projection does not increase the
   covering radius.  This is the abstract form of the fixed-radius step in
   `le:low_rank_induction` (papers/katznelson.tex, lines 1475--1479): project
   an ambient lattice point approximating a point of the orthogonal
   complement. -/
set_option maxHeartbeats 800000 in
theorem latticeCovering_orthogonalProjection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (L : Submodule ℤ E) {R : ℝ}
    (hcover : LatticeCovering L R) :
    LatticeCovering
      (L.map ((Submodule.orthogonalProjectionOnto (𝕜 := ℝ) U).toLinearMap.restrictScalars ℤ)) R := by
  intro x
  obtain ⟨y, hy⟩ := hcover (x : E)
  let P : E →ₗ[ℝ] U :=
    (Submodule.orthogonalProjectionOnto (𝕜 := ℝ) U).toLinearMap
  let z : U := P (y : E)
  have hz : z ∈ L.map
      ((Submodule.orthogonalProjectionOnto (𝕜 := ℝ) U).toLinearMap.restrictScalars ℤ) := by
    refine Submodule.mem_map.mpr ⟨y, y.property, ?_⟩
    rfl
  refine ⟨⟨z, hz⟩, ?_⟩
  rw [dist_eq_norm]
  have hxP : P (x : E) = x := by
    dsimp [P]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x
  have hPsub : P ((x : E) - (y : E)) = x - z := by
    dsimp [z]
    rw [map_sub, hxP]
  have hnonexp : ‖P ((x : E) - (y : E))‖ ≤
      ‖(x : E) - (y : E)‖ := by
    change ‖(Submodule.orthogonalProjectionOnto (𝕜 := ℝ) U)
        ((x : E) - (y : E))‖ ≤ ‖(x : E) - (y : E)‖
    exact Submodule.norm_orthogonalProjectionOnto_apply_le _ _
  change ‖x - z‖ ≤ R
  rw [← hPsub]
  exact hnonexp.trans (by simpa [dist_eq_norm] using hy)

/- [derived consequence, paper `le:ballvol`, lines 463--478] The
   manuscript's ball-count estimate uses the intrinsic covering radius.  This
   deterministic form records its actual unit-ball constant, so callers over
   varying subspaces can prove that their implicit constant is uniform. -/
set_option maxHeartbeats 800000 in
theorem lattice_ball_count_of_latticeCovering_unitBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (mu : Measure E) [Measure.IsAddHaarMeasure mu] {T R : ℝ}
    (hT : 0 < T) (hcover : LatticeCovering L R) :
    (Set.ncard {v : L | ‖(v : E)‖ ≤ T} : ℝ) ≤
      mu.real (Metric.closedBall (0 : E) 1) *
        (T + R) ^ Module.finrank ℝ E *
          (ZLattice.covolume L mu)⁻¹ := by
  let S : Set L := {v : L | ‖(v : E)‖ ≤ T}
  let F : Set E := latticeVoronoiDomain L
  have hRintr : latticeCoveringRadius L ≤ R :=
    latticeCoveringRadius_le_of_latticeCovering L hcover
  have hR : 0 ≤ R :=
    (latticeCoveringRadius_nonneg L).trans hRintr
  have hTR : 0 ≤ T + R := by linarith
  have hS : S.Finite := by
    simpa [S] using lattice_ball_finite L
  have hFbounded : Bornology.IsBounded F := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : E)]
    refine ⟨latticeCoveringRadius L, ?_⟩
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_latticeCoveringRadius_of_mem_latticeVoronoiDomain L hx
  have hFtop : mu F ≠ ⊤ := ne_of_lt hFbounded.measure_lt_top
  have hfund : IsAddFundamentalDomain L F mu := by
    exact latticeVoronoiDomain_isAddFundamentalDomain L mu
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
      _ ≤ T + R := add_le_add hvS
        ((norm_le_latticeCoveringRadius_of_mem_latticeVoronoiDomain L hy).trans
          hRintr)
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
      ZLattice.covolume_eq_measure_fundamentalDomain L mu hfund]
    exact hmeasure_le
  have hcovpos : 0 < ZLattice.covolume L mu := ZLattice.covolume_pos L mu
  have hdiv :
      (Set.ncard S : ℝ) ≤
        ((T + R) ^ Module.finrank ℝ E *
          mu.real (Metric.closedBall (0 : E) 1)) /
          ZLattice.covolume L mu :=
    (le_div_iff₀ hcovpos).2 hcard
  simpa [S, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

/- [derived consequence, paper `le:ballvol`, lines 463--478] Existential
   presentation of the preceding deterministic ball-count bound, retained
   for callers that only need a positive implicit constant. -/
theorem lattice_ball_count_of_latticeCovering
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (mu : Measure E) [Measure.IsAddHaarMeasure mu] {T R : ℝ}
    (hT : 0 < T) (hcover : LatticeCovering L R) :
    ∃ C : ℝ, 0 < C ∧
      (Set.ncard {v : L | ‖(v : E)‖ ≤ T} : ℝ) ≤
        C * (T + R) ^ Module.finrank ℝ E *
          (ZLattice.covolume L mu)⁻¹ := by
  let C : ℝ := mu.real (Metric.closedBall (0 : E) 1)
  have hC : 0 < C := by
    dsimp [C]
    rw [MeasureTheory.measureReal_def]
    apply ENNReal.toReal_pos
    · exact (Metric.measure_closedBall_pos mu 0 zero_lt_one).ne'
    · exact measure_closedBall_lt_top.ne
  refine ⟨C, hC, ?_⟩
  simpa [C] using
    (lattice_ball_count_of_latticeCovering_unitBall L mu hT hcover)

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

/- The cellwise argument above is independent of the particular half-open
fundamental parallelepiped.  This version records that fact explicitly for a
measurable bounded fundamental domain `F`; it is the bridge back to the
Voronoi notation used in the manuscript. -/
theorem integral_vadd_fundamentalDomain (F : Set E) (g : E → ℝ) (v : L) :
    ∫ x in v +ᵥ F, g x
        ∂(μHE[Module.finrank ℝ E] : Measure E) =
      ∫ x in F, g ((v : E) + x)
        ∂(μHE[Module.finrank ℝ E] : Measure E) := by
  let mu : Measure E := (μHE[Module.finrank ℝ E] : Measure E)
  have hmp := measurePreserving_add_left mu (v : E)
  have hemb :=
    (Homeomorph.addLeft (v : E)).toMeasurableEquiv.measurableEmbedding
  have hset : v +ᵥ F = (v : E) +ᵥ F := by
    ext x
    rfl
  rw [hset, ← Set.image_vadd]
  simpa only [vadd_eq_add, mu] using hmp.setIntegral_image_emb hemb g F

theorem summable_integral_fundamentalDomain (F : Set E)
    (hfund : IsAddFundamentalDomain L F
      (μHE[Module.finrank ℝ E] : Measure E))
    (g : E → ℝ)
    (hg : Integrable g
      (μHE[Module.finrank ℝ E] : Measure E)) :
    Summable (fun v : L =>
      ∫ x in F, g ((v : E) + x)
        ∂(μHE[Module.finrank ℝ E] : Measure E)) := by
  let mu : Measure E := (μHE[Module.finrank ℝ E] : Measure E)
  change IsAddFundamentalDomain L F mu at hfund
  let _ : VAddInvariantMeasure L E mu :=
    ⟨fun v s _ => by
      change mu ((fun x : E => (v : E) + x) ⁻¹' s) = mu s
      exact measure_preimage_add mu (v : E) s⟩
  have hsumIntegrable : Integrable g
      (Measure.sum fun v : L => mu.restrict (v +ᵥ F)) := by
    rw [hfund.sum_restrict]
    exact hg
  have hnormCells : Summable (fun v : L =>
      ∫ x in F, ‖g ((v : E) + x)‖ ∂mu) := by
    refine hsumIntegrable.summable_integral.congr (fun v => ?_)
    change (∫ x in v +ᵥ F, ‖g x‖ ∂mu) =
      ∫ x in F, ‖g ((v : E) + x)‖ ∂mu
    exact integral_vadd_fundamentalDomain L F (fun x => ‖g x‖) v
  apply Summable.of_norm
  exact hnormCells.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun v => norm_integral_le_integral_norm
      (fun x => g ((v : E) + x)))

theorem dist_scaled_add_fundamentalDomain_le (F : Set E) (R : ℝ)
    (hFbound : ∀ x : E, x ∈ F → ‖x‖ ≤ R)
    {T : ℝ} (hT : 0 < T) (v : L) {x : E} (hx : x ∈ F) :
    dist (T⁻¹ • ((v : E) + x)) (T⁻¹ • (v : E)) ≤ R / T := by
  have hxnorm := hFbound x hx
  have hTinv : 0 ≤ T⁻¹ := inv_nonneg.mpr hT.le
  calc
    dist (T⁻¹ • ((v : E) + x)) (T⁻¹ • (v : E)) = T⁻¹ * ‖x‖ := by
      rw [dist_eq_norm, ← smul_sub, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hTinv]
    _ ≤ T⁻¹ * R := mul_le_mul_of_nonneg_left hxnorm hTinv
    _ = R / T := by rw [div_eq_mul_inv, mul_comm]

theorem cell_integral_error_bound_fundamentalDomain
    (F : Set E) (R : ℝ) (hF : MeasurableSet F)
    (hFbound : ∀ x : E, x ∈ F → ‖x‖ ≤ R) (hRpos : 0 < R)
    (f : E → ℝ) (h_f : Admissible f) {T : ℝ} (hT : 0 < T)
    (v : L) (hRadius : R / T ≤ 1) :
    |∫ x in F, (f (T⁻¹ • (v : E)) - f (T⁻¹ • ((v : E) + x)))
        ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
      ∫ x in F, errorFunction f (T⁻¹ • ((v : E) + x)) (R / T)
        ∂(μHE[Module.finrank ℝ E] : Measure E) := by
  let mu : Measure E := (μHE[Module.finrank ℝ E] : Measure E)
  let ε := R / T
  have hε : 0 < ε := div_pos hRpos hT
  have hbase : Integrable
      (fun x : E => errorFunction f (T⁻¹ • x) ε) mu := by
    exact h_f.scaled_error_integrable hT hε hRadius
  have htranslated : Integrable
      (fun x : E => errorFunction f (T⁻¹ • ((v : E) + x)) ε) mu := by
    have hmp := measurePreserving_add_left mu (v : E)
    simpa [Function.comp_def] using hmp.integrable_comp_of_integrable hbase
  rw [← Real.norm_eq_abs]
  change ‖∫ x in F,
      (f (T⁻¹ • (v : E)) - f (T⁻¹ • ((v : E) + x))) ∂mu‖ ≤
    ∫ x in F, errorFunction f (T⁻¹ • ((v : E) + x)) ε ∂mu
  apply norm_integral_le_of_norm_le htranslated.restrict
  filter_upwards [ae_restrict_mem hF] with x hx
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact h_f.abs_sub_le_errorFunction
    (dist_scaled_add_fundamentalDomain_le L F R hFbound hT v hx)

theorem tsum_cell_integral_error_bound_fundamentalDomain
    (F : Set E) (R : ℝ) (hF : MeasurableSet F)
    (hfund : IsAddFundamentalDomain L F
      (μHE[Module.finrank ℝ E] : Measure E))
    (hFbound : ∀ x : E, x ∈ F → ‖x‖ ≤ R) (hRpos : 0 < R)
    (f : E → ℝ) (h_f : Admissible f) {T : ℝ} (hT : 0 < T)
    (hRadius : R / T ≤ 1) :
    |∑' v : L, ∫ x in F,
        (f (T⁻¹ • (v : E)) - f (T⁻¹ • ((v : E) + x)))
        ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
      ∫ x : E, errorFunction f (T⁻¹ • x) (R / T)
        ∂(μHE[Module.finrank ℝ E] : Measure E) := by
  let mu : Measure E := (μHE[Module.finrank ℝ E] : Measure E)
  change IsAddFundamentalDomain L F mu at hfund
  let ε : ℝ := R / T
  let g : E → ℝ := fun x => errorFunction f (T⁻¹ • x) ε
  let a : L → ℝ := fun v =>
    ∫ x in F, f (T⁻¹ • (v : E)) - f (T⁻¹ • ((v : E) + x)) ∂mu
  let b : L → ℝ := fun v => ∫ x in F, g ((v : E) + x) ∂mu
  have hε : 0 < ε := div_pos hRpos hT
  have hbase : Integrable g mu := by
    exact h_f.scaled_error_integrable hT hε hRadius
  let _ : VAddInvariantMeasure L E mu :=
    ⟨fun v s _ => by
      change mu ((fun x : E => (v : E) + x) ⁻¹' s) = mu s
      exact measure_preimage_add mu (v : E) s⟩
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
    exact integral_vadd_fundamentalDomain L F g v
  have hba : ∀ v, ‖a v‖ ≤ b v := by
    intro v
    dsimp only [a, b, g, ε, mu]
    rw [Real.norm_eq_abs]
    exact cell_integral_error_bound_fundamentalDomain L F R hF hFbound hRpos f h_f hT v
      hRadius
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

theorem covolume_mul_latticeSum_sub_integral_le_fundamentalDomain
    (F : Set E) (R : ℝ) (hF : MeasurableSet F)
    (hfund : IsAddFundamentalDomain L F
      (μHE[Module.finrank ℝ E] : Measure E))
    (hFbound : ∀ x : E, x ∈ F → ‖x‖ ≤ R) (hRpos : 0 < R)
    (f : E → ℝ) (h_f : Admissible f) {T : ℝ} (hT : 0 < T)
    (hRadius : R / T ≤ 1) :
    |ZLattice.covolume L
          (μHE[Module.finrank ℝ E] : Measure E) *
        (∑' v : L, f (T⁻¹ • (v : E))) -
        ∫ x : E, f (T⁻¹ • x)
          ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
      ∫ x : E, errorFunction f (T⁻¹ • x) (R / T)
        ∂(μHE[Module.finrank ℝ E] : Measure E) := by
  let mu : Measure E := (μHE[Module.finrank ℝ E] : Measure E)
  change IsAddFundamentalDomain L F mu at hfund
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
    exact summable_integral_fundamentalDomain L F hfund scaled hscaled
  have hFbounded : Bornology.IsBounded F := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : E)]
    refine ⟨R, ?_⟩
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hFbound x hx
  have hFfinite : mu F ≠ ⊤ := by
    exact ne_of_lt hFbounded.measure_lt_top
  have hcellError (v : L) :
      cellError v = ZLattice.covolume L mu * scaled (v : E) - cellIntegral v := by
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
      ZLattice.covolume L mu * scaled (v : E) -
        ∫ x in F, scaled ((v : E) + x) ∂mu
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L mu hfund]
  have hintegral : ∫ x : E, scaled x ∂mu = ∑' v, cellIntegral v := by
    rw [hfund.integral_eq_tsum'' scaled hscaled]
    apply tsum_congr
    intro v
    apply integral_congr_ae
    filter_upwards with x
    rfl
  have hidentity :
      ZLattice.covolume L mu * (∑' v : L, scaled (v : E)) -
          ∫ x : E, scaled x ∂mu =
        ∑' v, cellError v := by
    calc
      ZLattice.covolume L mu * (∑' v : L, scaled (v : E)) -
            ∫ x : E, scaled x ∂mu =
          (∑' v : L, ZLattice.covolume L mu * scaled (v : E)) -
            ∑' v, cellIntegral v := by
        rw [tsum_mul_left, hintegral]
      _ = ∑' v : L,
          (ZLattice.covolume L mu * scaled (v : E) - cellIntegral v) :=
        ((hlattice.mul_left _).tsum_sub hcells).symm
      _ = ∑' v, cellError v := by
        apply tsum_congr
        intro v
        exact (hcellError v).symm
  change |ZLattice.covolume L mu * (∑' v : L, scaled (v : E)) -
      ∫ x : E, scaled x ∂mu| ≤
    ∫ x : E, errorFunction f (T⁻¹ • x) (R / T) ∂mu
  rw [hidentity]
  exact tsum_cell_integral_error_bound_fundamentalDomain L F R hF hfund hFbound hRpos f h_f hT
    hRadius

theorem latticeRiemann_estimate_of_fundamentalDomain
    (F : Set E) (R : ℝ) (hF : MeasurableSet F)
    (hfund : IsAddFundamentalDomain L F
      (μHE[Module.finrank ℝ E] : Measure E))
    (hFbound : ∀ x : E, x ∈ F → ‖x‖ ≤ R) (hRpos : 0 < R)
    (f : E → ℝ) (h_f : Admissible f) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      R / T ≤ 1 →
      |(∑' v : L, f (T⁻¹ • (v : E))) /
            T ^ Module.finrank ℝ E -
          (ZLattice.covolume L
            (μHE[Module.finrank ℝ E] : Measure E))⁻¹ *
            ∫ x : E, f x
              ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
        Cₐ * R /
          (ZLattice.covolume L
            (μHE[Module.finrank ℝ E] : Measure E) * T) := by
  obtain ⟨Cₐ, hCₐ, herror⟩ := h_f.exists_error_bound_ambient
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  let q : ℕ := Module.finrank ℝ E
  let scale : ℝ := T ^ q
  let covol : ℝ := ZLattice.covolume L
    (μHE[Module.finrank ℝ E] : Measure E)
  let latticeSum : ℝ := ∑' v : L, f (T⁻¹ • (v : E))
  let ambientIntegral : ℝ :=
    ∫ x : E, f x ∂(μHE[Module.finrank ℝ E] : Measure E)
  let ε : ℝ := R / T
  have hε : 0 < ε := div_pos hRpos hT
  have hscale : 0 < scale := pow_pos hT q
  have hraw := covolume_mul_latticeSum_sub_integral_le_fundamentalDomain
    L F R hF hfund hFbound hRpos f h_f hT hRadius
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
  have hnormalized :
      |covol * (latticeSum / scale) - ambientIntegral| ≤ Cₐ * R / T := by
    rw [hidentity, abs_div, abs_of_pos hscale]
    apply (div_le_iff₀ hscale).2
    simpa [ε, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hraw'
  have hcovol : 0 < covol := by
    exact ZLattice.covolume_pos L
      (μHE[Module.finrank ℝ E] : Measure E)
  have hidentity' :
      latticeSum / scale - covol⁻¹ * ambientIntegral =
        (covol * (latticeSum / scale) - ambientIntegral) / covol := by
    field_simp [hcovol.ne']
  have hrhs : Cₐ * R / (covol * T) =
      (Cₐ * R / T) / covol := by
    field_simp [hcovol.ne', hT.ne']
  change |latticeSum / scale - covol⁻¹ * ambientIntegral| ≤
    Cₐ * R / (covol * T)
  rw [hidentity', abs_div, abs_of_pos hcovol, hrhs]
  exact (div_le_div_iff_of_pos_right hcovol).2 hnormalized

end CellEstimate

/- The exact manuscript-facing form of the Riemann estimate.  The Voronoi
cell is now used as the fundamental domain, so its radius is the intrinsic
covering radius from the paper rather than the auxiliary basis radius. -/
section IntrinsicVoronoiRiemann

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [ProperSpace E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

theorem latticeVoronoiRiemann_estimate
    (hRpos : 0 < latticeCoveringRadius L)
    (f : E → ℝ) (h_f : Admissible f) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      latticeCoveringRadius L / T ≤ 1 →
      |(∑' v : L, f (T⁻¹ • (v : E))) /
            T ^ Module.finrank ℝ E -
          (ZLattice.covolume L
            (μHE[Module.finrank ℝ E] : Measure E))⁻¹ *
            ∫ x : E, f x
              ∂(μHE[Module.finrank ℝ E] : Measure E)| ≤
        Cₐ * latticeCoveringRadius L /
          (ZLattice.covolume L
            (μHE[Module.finrank ℝ E] : Measure E) * T) := by
  let F : Set E := latticeVoronoiDomain L
  have hF : MeasurableSet F := by
    exact isClosed_latticeVoronoiDomain L |>.measurableSet
  have hfund : IsAddFundamentalDomain L F
      (μHE[Module.finrank ℝ E] : Measure E) := by
    exact latticeVoronoiDomain_isAddFundamentalDomain L
      (μHE[Module.finrank ℝ E] : Measure E)
  have hFbound : ∀ x : E, x ∈ F → ‖x‖ ≤ latticeCoveringRadius L := by
    intro x hx
    exact norm_le_latticeCoveringRadius_of_mem_latticeVoronoiDomain L hx
  exact latticeRiemann_estimate_of_fundamentalDomain L F
    (latticeCoveringRadius L) hF hfund hFbound hRpos f h_f

end IntrinsicVoronoiRiemann

end Katznelson
