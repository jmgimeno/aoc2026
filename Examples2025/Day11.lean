import Aoc2026.Util.Parse
import Std.Data.HashMap

open Aoc2026 Std

namespace Examples2025.Day11

/-! ## Day 11: memoization with `StateM` instead of `&mut HashMap` -/
abbrev Graph := HashMap String (Array String)
abbrev Memo := HashMap String Nat

def parseGraph (input : String) : Except String Graph :=
  (linesOf input).foldlM (init := {}) fun g line =>
    match line.splitOn ": " with
    | [src, dst] => return g.insert src ((dst.splitOn " ").toArray)
    | _ => throw s!"invalid line: {line}"

partial def go (g : Graph) (target node : String) : StateM Memo Nat := do
  if node == target then return 1
  if let some v := (← get)[node]? then return v
  let mut total := 0
  for next in g.getD node #[] do
    total := total + (← go g target next)
  modify (·.insert node total)
  return total

def countPaths (g : Graph) (src target : String) : Nat :=
  (go g target src).run' {} |>.run

def part1 (g : Graph) : Nat := countPaths g "you" "out"
def part2 (g : Graph) : Nat :=
  countPaths g "svr" "fft" * countPaths g "fft" "dac" * countPaths g "dac" "out"
  + countPaths g "svr" "dac" * countPaths g "dac" "fft" * countPaths g "fft" "out"

def ex1 := "aaa: you hhh\nyou: bbb ccc\nbbb: ddd eee\nccc: ddd eee fff\nddd: ggg\neee: out\nfff: out\nggg: out\nhhh: ccc fff iii\niii: out"
def ex2 := "svr: aaa bbb\naaa: fft\nfft: ccc\nbbb: tty\ntty: ccc\nccc: ddd eee\nddd: hub\nhub: fff\neee: dac\ndac: fff\nfff: ggg hhh\nggg: out\nhhh: out"
#guard (parseGraph ex1).toOption.map part1 == some 5
#guard (parseGraph ex2).toOption.map part2 == some 2

end Examples2025.Day11
