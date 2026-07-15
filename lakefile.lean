import Lake
open Lake DSL

package «HarperStabilityLean» where

require BooleanIsoperimetry from git
  "https://github.com/AlexeyMilovanov/BooleanIsoperimetry" @ "v4.28.0"

lean_lib «HarperStability» where

lean_lib «AverageHarperStability» where

-- Standalone modules used by leanprover/comparator.  `Challenge` imports only
-- Mathlib; `Solution` connects the trusted statement to the checked theorem.
lean_lib «Challenge» where

lean_lib «Solution» where
