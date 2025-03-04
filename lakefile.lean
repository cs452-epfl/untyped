import Lake
open Lake DSL

package «fos» {
  -- add package configuration options here
}

lean_lib «Fos» {
  -- add library configuration options here
}

require "leanprover-community" / "mathlib"

@[default_target]
lean_exe «fos» {
  root := `Main
}
