namespace Examples2025.Day01Verified

structure Move where
  right : Bool
  steps : Int

def step (pos : Int) (m : Move) : Int :=
  (if m.right then pos + m.steps else pos - m.steps) % 100

/-- Solution: the usual loop. -/
def part1 (moves : List Move) : Nat := Id.run do
  let mut position : Int := 50
  let mut password := 0
  for m in moves do
    position := step position m
    if position == 0 then password := password + 1
  return password

/-- Specification: the positions after each turn. -/
def positions (p : Int) : List Move → List Int
  | [] => []
  | m :: ms => step p m :: positions (step p m) ms

def spec (moves : List Move) : Nat := (positions 50 moves).count 0

/-- The Rust comment, as a theorem. -/
theorem step_in_range (p : Int) (m : Move) : 0 ≤ step p m ∧ step p m < 100 := by
  unfold step; split <;> omega

theorem positions_in_range (p q : Int) (ms : List Move) (h : q ∈ positions p ms) :
    0 ≤ q ∧ q < 100 := by
  induction ms generalizing p with
  | nil => simp [positions] at h
  | cons m ms ih =>
    simp only [positions, List.mem_cons] at h
    rcases h with rfl | h
    · exact step_in_range p m
    · exact ih _ h

def loop (p : Int) (acc : Nat) : List Move → Nat
  | [] => acc
  | m :: ms => loop (step p m) (if step p m == 0 then acc + 1 else acc) ms

theorem loop_eq (p : Int) (acc : Nat) (ms : List Move) :
    loop p acc ms = acc + (positions p ms).count 0 := by
  induction ms generalizing p acc with
  | nil => simp [loop, positions]
  | cons m ms ih =>
    simp only [loop, positions, ih, List.count_cons]
    by_cases h : step p m = 0 <;> simp [h] <;> omega

def ex : List Move := [⟨false,68⟩,⟨false,30⟩,⟨true,48⟩,⟨false,5⟩,⟨true,60⟩,⟨false,55⟩,⟨false,1⟩,⟨false,99⟩,⟨true,14⟩,⟨false,82⟩]
#guard part1 ex == 3
#guard spec ex == 3
example : part1 ex = 3 := by native_decide
example : part1 ex = 3 := by decide +kernel

theorem part1_eq_loop (ms : List Move) : part1 ms = loop 50 0 ms := by
  suffices h : ∀ (ms : List Move) (p : Int) (a : Nat),
      (Id.run do
        let mut position := p
        let mut password := a
        for m in ms do
          position := step position m
          if position == 0 then password := password + 1
        return password) = loop p a ms from h ms 50 0
  intro ms
  induction ms with
  | nil => intro p a; simp [loop]
  | cons m ms ih =>
    intro p a
    have := ih (step p m) (if step p m == 0 then a + 1 else a)
    simp only [Id.run, List.forIn_cons, loop] at this ⊢
    by_cases h : step p m = 0 <;> simp_all

theorem part1_correct (ms : List Move) : part1 ms = spec ms := by
  simp [part1_eq_loop, loop_eq, spec]

end Examples2025.Day01Verified
