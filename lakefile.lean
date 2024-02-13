import Lake
open Lake DSL

package «PrimeNumberTheoremAnd»

@[default_target]
lean_lib «PrimeNumberTheoremAnd»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "f9d8675"

require EulerProducts from git
  "https://github.com/MichaelStollBayreuth/EulerProducts.git" @ "422e323"

meta if get_config? env = some "dev" then require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "780bbec"
