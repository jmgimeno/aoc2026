import Aoc2026
import Examples2025.Day01
import Examples2025.Day04
import Examples2025.Day05

/-!
Tests that read input files, run with `lake test` from the project root.

The examples from each statement live next to the solution as `#guard`. This file is for
what `#guard` cannot do: read input files.

`data2025` holds only the examples from the statements, so it is committed. Real puzzle
inputs must not be published: they go in `data`, which is git-ignored, so a missing file is
reported as skipped instead of failing on machines without the inputs.
-/

open Aoc2026

inductive Outcome where
  | passed | failed | skipped
  deriving BEq

/-- Runs `part` on the contents of `path` and compares the answer with `expected`. -/
def check (name : String) (path : System.FilePath) (expected : String)
    (part : String → Except String String) : IO Outcome := do
  unless ← path.pathExists do
    IO.println s!"skip {name}: {path} not found"
    return .skipped
  try
    let actual ← IO.ofExcept (part (← readFileAsString path))
    if actual == expected then
      IO.println s!"ok   {name}"
      return .passed
    IO.println s!"FAIL {name}: expected {expected}, got {actual}"
    return .failed
  catch e =>
    IO.println s!"FAIL {name}: {e}"
    return .failed

def main : IO UInt32 := do
  let outcomes := #[
    ← check "2025 day01 part1" "data2025/day01.txt" "3" Examples2025.Day01.solution.part1,
    ← check "2025 day01 part2" "data2025/day01.txt" "6" Examples2025.Day01.solution.part2,
    ← check "2025 day04 part1" "data2025/day04.txt" "13" Examples2025.Day04.solution.part1,
    ← check "2025 day04 part2" "data2025/day04.txt" "43" Examples2025.Day04.solution.part2,
    ← check "2025 day05 part1" "data2025/day05.txt" "3" Examples2025.Day05.solution.part1,
    ← check "2025 day05 part2" "data2025/day05.txt" "14" Examples2025.Day05.solution.part2
  ]
  let count (o : Outcome) := (outcomes.filter (· == o)).size
  IO.println s!"{count .passed} passed, {count .failed} failed, {count .skipped} skipped"
  return if count .failed == 0 then 0 else 1
