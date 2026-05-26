import Lake
open Lake DSL

package "alphaproof-nexus" where
  -- Use existing .lake/packages layout
  precompileModules := false

require "leanprover-community" / "mathlib" @ git "master"

lean_lib Erdos1 where
  srcDir := "problems/1"
lean_lib Erdos25 where
  srcDir := "problems/25"
lean_lib Erdos634 where
  srcDir := "problems/634"
lean_lib ErdosLib where
  srcDir := "ErdosLib"
lean_lib Erdos364 where
  srcDir := "problems/364"

