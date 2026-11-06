# CLAUDE.md

Advent of Code 2026 in Lean 4. The goal is to **learn Lean as a programming language**, not
just to get answers. The owner has basic experience with Lean as a theorem prover, and a lot
of experience with AoC in Java, Scala, Python and Rust.

`README.md` covers the layout, the commands and the daily steps. Do not repeat it here.

## Working with the owner

- Reply in the language of the owner's message, which may be Spanish, Catalan or English.
- Everything inside the repo is in English: identifiers, comments, docstrings, error
  messages and documentation.
- Teach rather than solve. Explain idioms and trade-offs, relate them to Rust or Scala, and
  let the owner write the puzzle solutions unless they ask otherwise.
- When they are planning or asking questions, answer and experiment in a scratch directory.
  Change the repo only when they ask for it, and commit only when they ask for it.
- Verify claims about Lean on the pinned toolchain before stating them. The API changes
  quickly, and memory of older versions is often wrong.
- Separate what was tested from what was not.

## Conventions

- Pinned to `leanprover/lean4:v4.35.0`. Do not upgrade during the event. Any dependency must
  have a revision matching that version.
- The boundary of the program speaks `String`: each day exposes
  `solution : Solution := Solution.of parse part1 part2`, with its own types inside.
- Parsers are functions named `X.parse : String → Except String X`, plus
  `instance : FromStr X := ⟨X.parse⟩`. Inside them, use `parseAs T s` for the generic parser:
  a bare `parse` would resolve to `X.parse` itself.
- Parse fields left to right, one `let x ← parser` per field.
- `#guard` for the statement examples, in the day's file. `check` in `Tests.lean` for files.
- Grid coordinates are `Int`, so stepping off the edge leaves the grid.
- Real puzzle inputs must not be published. They go in `data/`, which is git-ignored.
  `data2025/` holds only examples from the statements and is committed.
- `Examples2025` is a separate library, so `lake build` does not check it. After changing
  shared code, run `just examples`. Each file there has its own `namespace`.

## Lean pitfalls on this toolchain

- `Array` only updates in place when the reference is unique. Keeping the old value in a
  loop copies the whole array on every write.
- `Lean.RBMap` is deprecated: use `Std.TreeMap`. `HashMap.empty` does not exist: use `{}` or
  `emptyWithCapacity`.
- `trimAscii` and `drop` return slices, so add `.toString`. `String.lines` returns an iterator.
- `"".front` does not fail, it returns a default character.
- `Except` has no `BEq`, so write `(x).toOption == some y` in `#guard`.
- `#guard` runs in the interpreter and cannot do `IO`.
- `Nat` subtraction truncates. `%` on `Int` behaves like `rem_euclid`.
- Pure code can move past a timer: wrap it with `IO.lazyPure` when measuring.
- `mvcgen` is deprecated in favour of `vcgen`.
- `Std.Internal.Parsec` works but is internal, so its API may change.
- On macOS, `sed` does not support `\b`. Use `perl` for that.

## Not done or not verified yet

- The downloader has only been tested against a local server, never adventofcode.com.
- Batteries, Plausible and ParseIt have never been built here: downloading external code
  was blocked by the permission system. Batteries and Plausible have a `v4.35.0` tag. For
  ParseIt, use commit `fd28b1c6cc58b241ac0663bdebffe51cb37bbb52`, and check that the manifest
  pins `UnicodeBasic` to `6e48acac…`.
- The 2025 ports have only been tested with the statement examples, not the real inputs.
- A 2026 schedule was not confirmed. Since 2025 the format has been 12 puzzles.
- `Heap` and BFS helpers do not exist yet. The owner wants to write those themselves.
- No generator for new days: they are created by hand, on purpose.
