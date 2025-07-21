import Lake
open Lake DSL

package «leansimlean_runtime» where
  leanOptions := #[
    ⟨`pp.unicode.fun, false⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.fieldNotation, false⟩,
    ⟨`pp.letVarTypes, true⟩,
    ⟨`pp.proofs, true⟩,
    ⟨`pp.coercions, false⟩,
    ⟨`pp.numericTypes, true⟩,
    ⟨`pp.motives.all, true⟩,
    ⟨`pp.funBinderTypes, true⟩,
    ⟨`pp.structureInstanceTypes, true⟩
  ]

@[default_target]
lean_lib LeansimLeanRuntime where

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"f0957a7"
require metalib from git "https://github.com/reaslab/metalib.git" @ "main"
require Cli from git "https://github.com/leanprover/lean4-cli.git" @ "main"
