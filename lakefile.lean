laimport Lake
open Lake DSL

package «tpwlean» where
  -- Settings for the project

@[default_target]
lean_lib «Tpwlean» where
  -- The library name

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"
