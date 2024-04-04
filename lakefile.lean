import Lake
open Lake DSL

package «CoInd» {
  -- add package configuration options here
}

@[default_target]
lean_lib «CoInd» {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4"

--lean_exe «dijkstraMonad» {
--  root := `Main
--}
-- f759a3662ca93422c3c8281852dc352f9a7b5399
