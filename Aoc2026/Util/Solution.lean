/-!
The boundary of the program speaks `String`: the input is the text of a file and the
answer is the text you paste into the website. Each day keeps its own types inside and
exposes a `Solution`, so `Main` and the tests treat every day the same way.
-/

namespace Aoc2026

/-- A day as `Main` and the tests see it: from the whole input to the answer, as text. -/
structure Solution where
  part1 : String → Except String String
  part2 : String → Except String String

/-- Builds a `Solution` from a typed parser and two typed parts. -/
def Solution.of {α β γ : Type} [ToString β] [ToString γ]
    (parse : String → Except String α) (part1 : α → β) (part2 : α → γ) : Solution where
  part1 input := return toString (part1 (← parse input))
  part2 input := return toString (part2 (← parse input))

end Aoc2026
