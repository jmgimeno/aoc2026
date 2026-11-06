import Aoc2026.Util.Parse
import Aoc2026.Util.Solution

open Aoc2026

namespace Examples2025.Day01

/-! ## Day 01: `Vec<(char, i32)>` → structure + `FromStr` -/
/-- `steps` is a `Nat` because a distance cannot be negative, so a line like `R-5` is
rejected while parsing. The proof of part 2 relies on this. -/
structure Move where
  dir : Char
  steps : Nat

def parseDir (c : Char) : Except String Char :=
  match c with
  | 'R' | 'L' => pure c
  | c => throw s!"invalid direction: {c}"

/-- One `let x ← parser` per field, in the order the fields appear in the line.
Each `←` runs immediately and stops at the first error, like `?` in Rust.

Beware of blank lines: `"".front` does not fail, it returns a default character,
so an empty line reports the misleading `invalid direction: A`. -/
def Move.parse (l : String) : Except String Move := do
  let dir ← parseDir l.front
  let steps ← parseAs Nat (l.drop 1).toString
  return { dir, steps }

instance : FromStr Move := ⟨Move.parse⟩

/-
Alternative that parses the fields right to left. It also works, because `front` and
`drop` read the same immutable `l`, but `steps` runs first even though it is only used
inside the `match`. So `"Xa"` reports the integer error, not the direction one.

instance : FromStr Move where
  fromStr l := do
    let n ← parseAs Nat (l.drop 1).toString
    match l.front with
    | 'R' => return ⟨'R', n⟩
    | 'L' => return ⟨'L', n⟩
    | c => throw s!"invalid direction: {c}"
-/

def part1 (moves : Array Move) : Nat := Id.run do
  let mut position : Int := 50
  let mut password := 0
  for m in moves do
    position := (if m.dir == 'R' then position + m.steps else position - m.steps) % 100
    if position == 0 then password := password + 1
  return password

def part2 (moves : Array Move) : Int := Id.run do
  let mut position : Int := 50
  let mut password : Int := 0
  for m in moves do
    let old := position
    position := if m.dir == 'R' then position + m.steps % 100 else position - m.steps % 100
    password := password + m.steps / 100
    if position ≥ 100 || (old != 0 && position ≤ 0) then password := password + 1
    position := position % 100
  return password

def example1 := "L68\nL30\nR48\nL5\nR60\nL55\nL1\nL99\nR14\nL82"
#guard (parseLines Move (linesOf example1)).toOption.map part1 == some 3
#guard (parseLines Move (linesOf example1)).toOption.map part2 == some 6
#guard (parseLines Move #["R1", "X2"]).toOption.isNone
#guard (parseLines Move #["R-5"]).toOption.isNone
#eval (parseLines Move #["R1", "X2"]).map (·.size)

def parseInput (input : String) : Except String (Array Move) :=
  parseLines Move (linesOf input)

def solution : Solution := Solution.of parseInput part1 part2

#guard (solution.part1 example1).toOption == some "3"
#guard (solution.part2 example1).toOption == some "6"

end Examples2025.Day01
