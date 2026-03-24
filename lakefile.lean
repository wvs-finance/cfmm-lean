import Lake
open Lake DSL

package «cfmm-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- Reference libraries (not Lake deps — pinned to older Lean versions):
-- dpusceddu/lean4-amm (Lean 4.5.0)  — AMM state, swap rate, constant product proofs
-- verified-optimization/CvxLean     — verified convex optimization, DCP tactics
-- r-marche/MEV-formal (Lean 4.14.0) — MEV characterization, token preservation

@[default_target]
lean_lib CFMMLib where
  srcDir := "."
