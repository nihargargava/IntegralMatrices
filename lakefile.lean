import Lake
open Lake DSL

package katznelson_formal where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
  lean_lib Katznelson where
    roots := #[`Katznelson.Foundations, `Katznelson.Counting.PaperMetric,
      `Katznelson.Counting.Admissible,
      `Katznelson.Lattice, `Katznelson.Lifts, `Katznelson.Counting.FiniteField,
      `Katznelson.Counting.RankDrop, `Katznelson.Counting.Support,
      `Katznelson.Counting.RowSpaces, `Katznelson.Counting.RowLattice,
      `Katznelson.Counting.RiemannSum, `Katznelson.Counting.ControlledRiemann,
      `Katznelson.Counting.ControlledVoronoi,
      `Katznelson.Counting.SubspaceRiemann,
      `Katznelson.Counting.RowLatticeRiemann,
      `Katznelson.Counting.GeometryOfNumbers,
      `Katznelson.Counting.SuccessiveMinima,
      `Katznelson.Counting.MinkowskiSecond,
      `Katznelson.Counting.FiekerStehle,
      `Katznelson.Counting.CrudeHeight,
      `Katznelson.Counting.Echelon,
      `Katznelson.Counting.MinimumBound,
      `Katznelson.Counting.MinimumInjection,
      `Katznelson.Counting.MinimaSums,
      `Katznelson.Counting.CriticalRankOne,
      `Katznelson.Counting.CriticalMinima,
      `Katznelson.Counting.CriticalMinimaSums,
      `Katznelson.Counting.FixedRankError,
      `Katznelson.Counting.PaperMetricRowSpaces,
      `Katznelson.Counting.MainTermNormalization,
      `Katznelson.Counting.LiftCovolume,
      `Katznelson.Counting.UniformIntegral,
      `Katznelson.Counting.UniformRiemann,
      `Katznelson.Counting.UniformFiniteAssembly,
      `Katznelson.Counting.UniformHeightTail,
      `Katznelson.Counting.UniformHeightTailLiteral,
      `Katznelson.Counting.UniformLowerRank,
      `Katznelson.Counting.UniformLowerRankLiteral,
      `Katznelson.Counting.Schmidt,
      `Katznelson.Counting.LiftAverage,
      `Katznelson.MainTheorems, `Katznelson.FinalAssembly, `main]
