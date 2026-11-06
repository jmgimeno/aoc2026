import Aoc2026

open Aoc2026

/-- One entry per solved day, for example `("day01", Day01.solution)`. -/
def days : List (String × Solution) := []

def main : List String → IO UInt32
  | [day] => do
    let some solution := days.lookup day
      | IO.eprintln s!"unknown day: {day}"; return 1
    try
      let input ← readFileAsString s!"data/{day}.txt"
      IO.println s!"Part1: {← IO.ofExcept (solution.part1 input)}"
      IO.println s!"Part2: {← IO.ofExcept (solution.part2 input)}"
      return 0
    catch e =>
      IO.eprintln e
      return 1
  | _ => do
    IO.eprintln "usage: lake exe aoc2026 dayNN"
    return 1
