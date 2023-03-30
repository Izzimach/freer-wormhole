import Lake
open Lake DSL


-- solifugid-z holds transition systems/LTL/CTL used for model checking
require «solifugid-z» from git "https://gitlab.com/Izzimach/solifugid-z"@"5d99dd71841d272550886c3b1c7c76ada67fe04c"

package «freer-wormhole» {
  -- add package configuration options here
}

lean_lib FreerWormhole {
  -- add library configuration options here
}

lean_lib WormholeExamples {

}

lean_exe «freer-wormhole» {
  root := `Main
}

lean_exe petersonexclusion {
  root := `WormholeExamples.PetersonExclusion
}
