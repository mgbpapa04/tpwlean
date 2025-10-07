import Lake
open Lake DSL

package «tpwlean» where
  -- Settings for the project

-- This 'require' line must come BEFORE the library definition below.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Tpwlean» where
  -- The library name
