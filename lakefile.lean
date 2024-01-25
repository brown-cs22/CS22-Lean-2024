import Lake
open Lake DSL


require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.4.0"
require autograder from git "https://github.com/robertylewis/lean4-autograder-main" @ "864b34ce06d8536aec0c38e57448c17d1f83572a"

package «brown-cs22» {
  -- add package configuration options here
  moreServerOptions := #[⟨`autoImplicit, false⟩, ⟨`linter.unusedVariables, false⟩]
}

lean_lib BrownCs22 {
  -- add library configuration options here
  roots := #[`BrownCs22]
  globs := #[Glob.submodules `BrownCs22]
  moreServerOptions := #[⟨`autoImplicit, false⟩, ⟨`linter.unusedVariables, false⟩]
}

@[default_target]
lean_exe «brown-cs22» {
  root := `Main
}

lean_exe stripsols where
  root := `BrownCs22.StripSols
