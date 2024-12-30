import Lake
open Lake DSL

package «orderTheory» {
  -- add any package configuration options here
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.14.0"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib «OrderTheory» where
  moreLeanArgs := #[
    -- "-DrelaxedAutoImplicit=false",
    "-DautoImplicit=false"
       ]
  moreServerOptions := #[
    -- ⟨`relaxedAutoImplicit, false⟩,
    ⟨`autoImplicit, false⟩ ]
