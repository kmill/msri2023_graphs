import Lake
open Lake DSL

package «graphProjects» {
  -- add package configuration options here
}

lean_lib «GraphProjects» {
  -- add library configuration options here
}

@[default_target]
lean_exe «graphProjects» {
  root := `Main
}

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
