/-!
Reading and parsing of AoC inputs: the equivalent of the `common` crate
from the 2025 Rust solution.

Paths are relative to the project root, which is where `lake exe` is run from.
-/

namespace Aoc2026

/-- Equivalent of `std::str::FromStr`, with `String` errors. -/
class FromStr (α : Type) where
  fromStr : String → Except String α

instance : FromStr Nat where
  fromStr s :=
    match s.toNat? with
    | some n => .ok n
    | none => .error s!"not a natural number: \"{s}\""

instance : FromStr Int where
  fromStr s :=
    match s.toInt? with
    | some n => .ok n
    | none => .error s!"not an integer: \"{s}\""

/-- Equivalent of `s.parse::<T>()`: `parseAs Nat "42"`. -/
def parseAs (α : Type) [FromStr α] (s : String) : Except String α :=
  FromStr.fromStr s

/-- Equivalent of `str::lines`: a trailing empty line does not count. -/
def linesOf (s : String) : Array String :=
  s.lines.toArray.map toString

/-- Applies a parser to each line and reports which one failed. -/
def parseLinesWith {α : Type} (p : String → Except String α) (lines : Array String) :
    Except String (Array α) :=
  lines.mapIdxM fun i line =>
    match p line with
    | .ok x => .ok x
    | .error e => .error s!"line {i + 1}: {e}"

/-- Like `parseLinesWith`, using the `FromStr` instance. -/
def parseLines (α : Type) [FromStr α] (lines : Array String) : Except String (Array α) :=
  parseLinesWith FromStr.fromStr lines

/-- Equivalent of `read_file_as_string`: reads the file and trims both ends. -/
def readFileAsString (path : System.FilePath) : IO String := do
  let content ← IO.FS.readFile path
  return content.trimAscii.toString

/-- Equivalent of `read_file_as_lines`. -/
def readFileAsLines (path : System.FilePath) : IO (Array String) :=
  IO.FS.lines path

/-- Reads the file and applies a given parser to each line. -/
def readFileWith {α : Type} (p : String → Except String α) (path : System.FilePath) :
    IO (Array α) := do
  IO.ofExcept (parseLinesWith p (← readFileAsLines path))

/-- Equivalent of `read_file_as_elements::<T>`: `readFileAsElements Nat "data/day03.txt"`. -/
def readFileAsElements (α : Type) [FromStr α] (path : System.FilePath) : IO (Array α) :=
  readFileWith FromStr.fromStr path

end Aoc2026
