import Lake
open Lake DSL


-- solifugid-z holds transition systems/LTL/CTL used for model checking
require «solifugid-z» from git "https://gitlab.com/Izzimach/solifugid-z"@"b357ec497e4fe5b6beeea7eab4417ff2f1b7999a"

package «freer-wormhole» {
  -- add package configuration options here
}

lean_lib FreerWormhole {
  -- add library configuration options here
}

lean_exe «freer-wormhole» {
  root := `Main
}
