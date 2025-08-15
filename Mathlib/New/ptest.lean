import Mathlib.Tactic.MinImports
open Lean Elab Command
open Mathlib.Command.MinImports (getId previousInstName getDeclName)


elab "#test_getId" cmd:command : command => do
  elabCommand cmd
  logInfo m! "{(←getId cmd).getId}"

elab "#test_previousInstName" cmd:command : command => do
  elabCommand cmd
  logInfo m! "{previousInstName (←getId cmd).getId}"

elab "#test_getDeclName" cmd:command : command => do
  elabCommand cmd
  logInfo m! "{←getDeclName cmd}"


class C where

namespace n1
/-- info: instC_1    -/ #guard_msgs in #test_getId instance : C where
/-- info: instC_2    -/ #guard_msgs in #test_getId instance : C where
/-- info: instC_5    -/ #guard_msgs in #test_getId instance instC_5 : C where
end n1

namespace n2
/-- info: instC      -/ #guard_msgs in #test_previousInstName instance : C where
/-- info: instC_1    -/ #guard_msgs in #test_previousInstName instance : C where
/-- info: instC_4    -/ #guard_msgs in #test_previousInstName instance instC_5 : C where
end n2

namespace n3
/-- info: n3.instC   -/ #guard_msgs in #test_getDeclName instance : C where
/-- info: n3.instC_1 -/ #guard_msgs in #test_getDeclName instance : C where
/-- info: n3.instC_5 -/ #guard_msgs in #test_getDeclName instance instC_5 : C where
end n3

namespace n4
instance instC_1 : C where
/-- info: n4.instC_1 -/ #guard_msgs in #test_getDeclName instance : C where
-- should in fact be `n4.instC`
end n4

-- still doesn't work: in general there is no way to tell what the last created
-- instance was.

#check getDeclName

#check Environment.constants

-- goal:
-- codify what it is meant to do, possibly extract, provide tests, and refactor
-- general uses and comments.

-- module system make break this.
