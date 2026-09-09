import Lake
open Lake DSL

package katznelson_formal where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
  lean_lib Katznelson where
    roots := #[`Katznelson.Foundations, `Katznelson.Counting.Admissible,
      `Katznelson.Lattice, `Katznelson.Lifts, `Katznelson.Counting.FiniteField,
      `Katznelson.Counting.RankDrop, `Katznelson.Counting.Support,
      `Katznelson.Counting.RowSpaces, `Katznelson.Counting.RowLattice,
      `Katznelson.Counting.RiemannSum, `Katznelson.Counting.ControlledRiemann,
      `Katznelson.Counting.SubspaceRiemann,
      `Katznelson.Counting.RowLatticeRiemann,
      `Katznelson.Counting.Echelon,
      `Katznelson.Counting.Schmidt,
      `Katznelson.Counting.LiftAverage,
      `Katznelson.MainTheorems, `main]
