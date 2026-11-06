import Aoc2026.Util.Grid
import Aoc2026.Util.Solution

open Aoc2026

namespace Examples2025.Day04

/-! ## Day 04: a grid simulation with `Grid` -/

abbrev Diagram := Grid Bool

def accessibleLimit : Nat := 4

def parseInput : String → Except String Diagram :=
  Grid.parse (· == '@')

def countNeighbors (g : Diagram) (p : Pos) : Nat :=
  ((g.neighbors8 p).filter (g.getD · false)).size

def accessiblePapers (g : Diagram) : Array Pos :=
  (g.findAll id).filter (countNeighbors g · < accessibleLimit)

def part1 (g : Diagram) : Nat :=
  (accessiblePapers g).size

def part2 (diagram : Diagram) : Nat := Id.run do
  -- No `clone()` as in Rust: `diagram` is immutable, this is a new binding.
  let mut g := diagram
  let mut totalRemoved := 0
  repeat
    let toRemove := accessiblePapers g
    if toRemove.isEmpty then break
    totalRemoved := totalRemoved + toRemove.size
    for p in toRemove do
      g := g.set p false
  return totalRemoved

def solution : Solution := Solution.of parseInput part1 part2

def sample :=
  "..@@.@@@@.\n@@@.@.@.@@\n@@@@@.@.@@\n@.@@@@..@.\n@@.@@@@.@@\n" ++
  ".@@@@@@@.@\n.@.@.@.@@@\n@.@@@.@@@@\n.@@@@@@@@.\n@.@.@@@.@."

#guard (solution.part1 sample).toOption == some "13"
#guard (solution.part2 sample).toOption == some "43"

end Examples2025.Day04
