import Aoc2026.Util.Parse
import Aoc2026.Util.Solution

open Aoc2026

namespace Examples2025.Day05

/-! ## Day 05: input in two blocks -/
abbrev Rng := Nat × Nat
structure DB where
  ranges : Array Rng
  available : Array Nat

def parseRange (s : String) : Except String Rng :=
  match s.splitOn "-" with
  | [a, b] => return (← parseAs Nat a, ← parseAs Nat b)
  | _ => throw s!"invalid range: {s}"

def merge (rs : Array Rng) : Array Rng := Id.run do
  let sorted := rs.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
  let mut out : Array Rng := #[]
  for r in sorted do
    match out.back? with
    | some last =>
      if r.1 ≤ last.2 then out := out.pop.push (last.1, max last.2 r.2)
      else out := out.push r
    | none => out := out.push r
  return out

def DB.parse (s : String) : Except String DB := do
  match s.splitOn "\n\n" with
  | [top, bottom] =>
    let ranges ← parseLinesWith parseRange (linesOf top)
    let available ← parseLines Nat (linesOf bottom)
    return { ranges := merge ranges, available }
  | _ => throw "expected two blocks"

instance : FromStr DB := ⟨DB.parse⟩

def part1 (db : DB) : Nat :=
  (db.available.filter fun x => db.ranges.any fun r => r.1 ≤ x && x ≤ r.2).size
def part2 (db : DB) : Nat :=
  db.ranges.foldl (fun acc r => acc + (r.2 - r.1 + 1)) 0

def ex := "3-5\n10-14\n16-20\n12-18\n\n1\n5\n8\n11\n17\n32"
#guard (parseAs DB ex).toOption.map part1 == some 3
#guard (parseAs DB ex).toOption.map part2 == some 14

def solution : Solution := Solution.of DB.parse part1 part2

#guard (solution.part1 ex).toOption == some "3"
#guard (solution.part2 ex).toOption == some "14"

end Examples2025.Day05
