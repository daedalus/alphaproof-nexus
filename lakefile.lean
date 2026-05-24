import Lake
open Lake DSL

package "alphaproof-nexus" where
  -- Use existing .lake/packages layout
  precompileModules := true

require "leanprover-community" / "mathlib" @ git "master"

lean_lib Erdos1 where
  srcDir := "Erdos1"
lean_lib Erdos25 where
  srcDir := "Erdos25-evolve"
lean_lib Erdos634 where
  srcDir := "Erdos634"
