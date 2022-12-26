import Lake
open Lake DSL


-- solifugid-z holds transition systems/LTL/CTL used for model checking
require «solifugid-z» from git "https://gitlab.com/Izzimach/solifugid-z"@"3634b3735243332dbd65d7313a2a11ec3ae56d5b"

package «freer-wormhole» {
  -- add package configuration options here
}

lean_lib FreerWormhole {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe «freer-wormhole» {
  root := `Main
}
