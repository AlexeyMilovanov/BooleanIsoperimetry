import Lake
open Lake DSL

package «HarperStabilityLean» where

require BooleanIsoperimetry from git
  "https://github.com/AlexeyMilovanov/BooleanIsoperimetry" @ "v4.28.0"

lean_lib «HarperStability» where

lean_lib «AverageHarperStability» where
