# Advent of Code 2026 in Lean 4

My solutions to [Advent of Code](https://adventofcode.com/) 2026, written to learn
[Lean 4](https://lean-lang.org/) as a programming language.

The project structure comes from my
[2025 solutions in Rust](https://github.com/jmgimeno/aoc2025): before writing any 2026
code, I studied that repo and ported part of it. Those ports live in `Examples2025` as a
permanent reference.

| Rust (2025) | Lean (2026) |
| --- | --- |
| `common` crate | `Aoc2026/Util/Parse.lean` |
| `FromStr` | `FromStr`, a class defined in this project |
| `s.parse::<T>()` | `parseAs T s` |
| `read_file_as_elements::<T>` | `readFileAsElements T` |
| `Diagram` with `Vec<Vec<bool>>` | `Grid Bool`, over a flat `Array` |
| `part1(&INPUT)` in each `main.rs` | `Solution`, run from a single `Main.lean` |
| `#[test]` with the statement example | `#guard` |
| `#[test]` with the puzzle input | `check` in `Tests.lean` |
| `downloader` crate | `Downloader.lean` |

## Requirements

- [elan](https://github.com/leanprover/elan), which installs the Lean version pinned in
  `lean-toolchain`
- [just](https://github.com/casey/just), to run the recipes in the `justfile`
- `curl`, used by the downloader

## Layout

```text
Aoc2026/            2026 solutions
  Util/Parse.lean   input reading and parsing
  Util/Solution.lean  the common shape of a day
  Util/Grid.lean    two-dimensional grids and positions
Aoc2026.lean        imports every module of the library
Main.lean           runs one day and prints its answers
Examples2025/       reference ports of the 2025 solutions, some with proofs
data/               real puzzle inputs (git-ignored)
data2025/           statement examples used by the 2025 ports
Downloader.lean     input downloader
Tests.lean          tests that read input files
justfile            common commands
```

Puzzle inputs must not be published, so they only ever go in `data/`. `data2025/` holds
nothing but examples from the statements.

## Commands

Run them from the project root.

| Command | What it does |
| --- | --- |
| `just build` | Builds the 2026 solutions and checks their `#guard` tests |
| `just run day01` | Prints the answers of a day, using `data/day01.txt` |
| `just test` | Runs the tests that read input files |
| `just examples` | Builds `Examples2025`, including its proofs |
| `just download day01` | Downloads the input to `data/day01.txt` |

The downloader reads the session cookie from `.env`, which is git-ignored:

```text
AOC_COOKIE=your-session-cookie
```

## Answers are strings

The boundary of the program speaks `String`: the input is the text of a file, and the answer
is the text you paste into the website. Some answers are not even numbers.

Each day uses whatever types suit it inside, and exposes a `Solution`:

```lean
structure Solution where
  part1 : String → Except String String
  part2 : String → Except String String
```

`Solution.of` builds one from a typed parser and two typed parts, so no day has to convert
anything by hand. Since all days look the same from the outside, `Main.lean` is a table and
every test has the same form.

## Every day

Replace `01` with the number of the day.

**1. Download the input.**

```sh
just download day01
```

**2. Create `Aoc2026/Day01.lean`.** Write the parser, the two parts, a `#guard` for each
example in the statement, and the `solution` at the end:

```lean
import Aoc2026.Util.Parse
import Aoc2026.Util.Solution

namespace Aoc2026.Day01

structure Entry where
  value : Nat

def Entry.parse (line : String) : Except String Entry := do
  let value ← parseAs Nat line
  return { value }

instance : FromStr Entry := ⟨Entry.parse⟩

def parseInput (input : String) : Except String (Array Entry) :=
  parseLines Entry (linesOf input)

def part1 (entries : Array Entry) : Nat :=
  entries.foldl (· + ·.value) 0

def part2 (entries : Array Entry) : Nat :=
  entries.size

def solution : Solution := Solution.of parseInput part1 part2

def sample := "1\n2\n3"

#guard (solution.part1 sample).toOption == some "6"
#guard (solution.part2 sample).toOption == some "3"

end Aoc2026.Day01
```

**3. Register the day.** Add the module to `Aoc2026.lean`:

```lean
import Aoc2026.Day01
```

And add the solution to `days` in `Main.lean`:

```lean
def days : List (String × Solution) := [
  ("day01", Day01.solution)
]
```

**4. Check the examples.** A failing `#guard` makes the build fail, and the editor marks it
as you type.

```sh
just build
```

**5. Get the answers** and submit them.

```sh
just run day01
```

**6. Lock in the answers.** Add one `check` per part to the array in `main`, in `Tests.lean`:

```lean
← check "2026 day01 part1" "data/day01.txt" "1234" Day01.solution.part1,
← check "2026 day01 part2" "data/day01.txt" "2" Day01.solution.part2,
```

```sh
just test
```

From then on, the tests protect the solution against later changes to shared code.

## Tests

| Kind | Where | When it runs | Data |
| --- | --- | --- | --- |
| Statement examples | `#guard` in each `DayNN.lean` | At build time | Inline |
| Puzzle inputs | `check` in `Tests.lean` | `just test` | `data/` or `data2025/` |

- `#guard` runs in the interpreter and cannot read files, so keep it to small, fast
  examples.
- `just test` also builds the modules that `Tests.lean` imports, so it checks their
  `#guard` tests too.
- If an input file is missing, `check` reports `skip` and the run still succeeds. Read the
  summary line: a skipped test is not a passing test.

## Proofs

`Examples2025/Day01Part1Verified.lean`, `Examples2025/Day01Part2Verified.lean` and
`Examples2025/Day05Verified.lean` show the difference between computing an answer and proving
it correct.

The two day 1 files import `Day01.lean`, so their theorems are about the solution that
actually runs. `Day05Verified.lean` still verifies a separate model of `merge`. In all of
them, neither the parsers nor the link between a specification and the puzzle statement are
proved.
