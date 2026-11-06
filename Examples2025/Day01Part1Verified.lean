import Examples2025.Day01

open Examples2025.Day01

/-! Proofs about the real `Day01.part1`, which this file imports rather than copies. -/

namespace Examples2025.Day01Part1Verified

/-- One rotation, as `Day01.part1` computes it. -/
def step (pos : Int) (m : Move) : Int :=
  (if m.dir == 'R' then pos + m.steps else pos - m.steps) % 100

/-- Specification: the positions after each turn. -/
def positions (p : Int) : List Move → List Int
  | [] => []
  | m :: ms => step p m :: positions (step p m) ms

def spec (moves : Array Move) : Nat := (positions 50 moves.toList).count 0

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

def ex : Array Move :=
  #[⟨'L',68⟩,⟨'L',30⟩,⟨'R',48⟩,⟨'L',5⟩,⟨'R',60⟩,⟨'L',55⟩,⟨'L',1⟩,⟨'L',99⟩,⟨'R',14⟩,⟨'L',82⟩]
#guard part1 ex == 3
#guard spec ex == 3
example : part1 ex = 3 := by native_decide
example : part1 ex = 3 := by decide +kernel

/-- The state of the `for` is the pair `(position, password)`, and induction needs it to be
arbitrary, not the initial `(50, 0)`. Nothing here restates the loop of `part1`. -/
theorem part1_eq_loop (ms : Array Move) : part1 ms = loop 50 0 ms.toList := by
  simp only [part1, Id.run]
  rw [← Array.forIn_toList]
  generalize ms.toList = l
  change _ = loop ((50 : Int), (0 : Nat)).1 ((50 : Int), (0 : Nat)).2 l
  generalize ((50 : Int), (0 : Nat)) = s
  induction l generalizing s with
  | nil => simp [loop]; rfl
  | cons m l ih =>
    have := ih (step s.1 m, if step s.1 m == 0 then s.2 + 1 else s.2)
    simp [List.forIn_cons, loop, step] at this ⊢
    by_cases hd : m.dir = 'R' <;> simp only [hd, ite_true, ite_false] at this ⊢ <;>
      split at this <;> split <;> first | exact this | (exfalso; omega)

theorem part1_correct (ms : Array Move) : part1 ms = spec ms := by
  simp [part1_eq_loop, loop_eq, spec]

end Examples2025.Day01Part1Verified
