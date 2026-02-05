import Lake
open Lake DSL

package «borel_det» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩
  ]
  -- Lean can fail to create its default thread pool under the project's 6GB ulimit.
  -- For reproducible builds in this environment, force single-threaded elaboration.
  moreLeanArgs := #["-j", "1"]
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0"

@[default_target]
lean_lib «BorelDet» {
  -- add any library configuration options here
}
