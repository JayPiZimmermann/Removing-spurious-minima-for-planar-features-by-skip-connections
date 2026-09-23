import Lake
open Lake DSL

package «planar_skip_formalization» where
  -- no package-level options

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.4.0"

/-- The whole development: every module of this repository, rooted here.
Build the entry point with `lake build All`. -/
@[default_target]
lean_lib «PlanarSkip» where
  srcDir := "."
  roots := #[`All, `Beam, `BentRing, `Definitions, `Empirical, `Geometry, `Overview_definitions, `Overview_theorems, `Plain, `Planar, `Preliminaries, `Skip, `Theorems]
  moreLeanArgs := #["-M", "16384"]
