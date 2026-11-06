import Examples2025.Day01

open Examples2025.Day01

/-! Proofs about the real `Day01.part2`, which this file imports rather than copies. -/

namespace Examples2025.Day01Part2Verified

/-! ## Specification: the statement, click by click -/

def click (right : Bool) (p : Int) : Int :=
  (if right then p + 1 else p - 1) % 100

/-- The positions after each click of one rotation. -/
def clicks (right : Bool) (p : Int) : Nat → List Int
  | 0 => []
  | n + 1 => click right p :: clicks right (click right p) n

/-- Where one rotation ends, again click by click. -/
def turn (right : Bool) (p : Int) : Nat → Int
  | 0 => p
  | n + 1 => turn right (click right p) n

/-- Every position the dial goes through. -/
def trace (p : Int) : List Move → List Int
  | [] => []
  | m :: ms => clicks (m.dir == 'R') p m.steps ++ trace (turn (m.dir == 'R') p m.steps) ms

def spec (moves : Array Move) : Nat := (trace 50 moves.toList).count 0

/-! ## The arithmetic of `Day01.part2`, split into named pieces -/

def arrive (p : Int) (m : Move) : Int :=
  if m.dir == 'R' then p + (m.steps : Int) % 100 else p - (m.steps : Int) % 100

/-- Does the last partial turn reach 0? -/
def crosses (p : Int) (m : Move) : Bool :=
  arrive p m ≥ 100 || (p != 0 && arrive p m ≤ 0)

def ex : Array Move :=
  #[⟨'L',68⟩,⟨'L',30⟩,⟨'R',48⟩,⟨'L',5⟩,⟨'R',60⟩,⟨'L',55⟩,⟨'L',1⟩,⟨'L',99⟩,⟨'R',14⟩,⟨'L',82⟩]
#guard part2 ex == 6
#guard spec ex == 6
#guard part2 #[⟨'R', 1000⟩] == 10
#guard spec #[⟨'R', 1000⟩] == 10

/-! ## Properties -/

theorem click_in_range (r : Bool) (p : Int) : 0 ≤ click r p ∧ click r p < 100 := by
  unfold click; split <;> omega

/-- Turning right `n` clicks: the multiples of 100 in `(p, p + n]`. -/
theorem zeros_right (p : Int) (n : Nat) (h : 0 ≤ p ∧ p < 100) :
    (((clicks true p n).count 0 : Nat) : Int) = (p + n) / 100 := by
  induction n generalizing p with
  | zero => simp [clicks]; omega
  | succ n ih =>
    have hq := click_in_range true p
    have := ih _ hq
    simp only [clicks, List.count_cons]
    simp only [click] at *
    by_cases hz : (if true = true then p + 1 else p - 1) % 100 = 0 <;> simp_all <;> omega

/-- Turning left `n` clicks: the multiples of 100 in `[p - n, p)`. -/
theorem zeros_left (p : Int) (n : Nat) (h : 0 ≤ p ∧ p < 100) :
    (((clicks false p n).count 0 : Nat) : Int) = (p - 1) / 100 - (p - n - 1) / 100 := by
  induction n generalizing p with
  | zero => simp [clicks]
  | succ n ih =>
    have hq := click_in_range false p
    have := ih _ hq
    simp only [clicks, List.count_cons]
    simp only [click] at *
    by_cases hz : (if false = true then p + 1 else p - 1) % 100 = 0 <;> simp_all <;> omega

/-- The heart of part 2: the arithmetic counts exactly the clicks at 0. -/
theorem zeros_eq (p : Int) (m : Move) (h : 0 ≤ p ∧ p < 100) :
    (((clicks (m.dir == 'R') p m.steps).count 0 : Nat) : Int) =
      (m.steps : Int) / 100 + (if crosses p m then 1 else 0) := by
  rcases m with ⟨d, n⟩
  by_cases hd : d = 'R'
  · subst hd
    have := zeros_right p n h
    simp only [crosses, arrive]
    simp at this ⊢
    rw [this]
    split <;> omega
  · have hne : (d == 'R') = false := by simp [hd]
    simp only [crosses, arrive, hne]
    rw [zeros_left p n h]
    by_cases hp : p = 0 <;> simp [hp] <;> split <;> omega

/-- The arithmetic and the clicks agree on where the rotation ends. -/
theorem turn_eq (p : Int) (m : Move) (h : 0 ≤ p ∧ p < 100) :
    turn (m.dir == 'R') p m.steps = arrive p m % 100 := by
  rcases m with ⟨d, n⟩
  simp only [arrive]
  generalize (d == 'R') = r
  induction n generalizing p with
  | zero => simp [turn]; omega
  | succ n ih =>
    simp only [turn]
    rw [ih _ (click_in_range r p)]
    cases r <;> simp [click] <;> omega

def loop (p acc : Int) : List Move → Int
  | [] => acc
  | m :: ms =>
    loop (arrive p m % 100)
      (if crosses p m then acc + (m.steps : Int) / 100 + 1 else acc + (m.steps : Int) / 100) ms

theorem loop_eq (p acc : Int) (ms : List Move) (h : 0 ≤ p ∧ p < 100) :
    loop p acc ms = acc + ((trace p ms).count 0 : Nat) := by
  induction ms generalizing p acc with
  | nil => simp [loop, trace]
  | cons m ms ih =>
    have hn : 0 ≤ arrive p m % 100 ∧ arrive p m % 100 < 100 := by omega
    have hz := zeros_eq p m h
    simp only [loop, trace, List.count_append, turn_eq p m h, ih _ _ hn]
    split <;> simp_all <;> omega

/-- As in part 1, generalizes the state of the `for` instead of restating the loop. -/
theorem part2_eq_loop (ms : Array Move) : part2 ms = loop 50 0 ms.toList := by
  simp only [part2, Id.run]
  rw [← Array.forIn_toList]
  generalize ms.toList = l
  change _ = loop ((50 : Int), (0 : Int)).1 ((50 : Int), (0 : Int)).2 l
  generalize ((50 : Int), (0 : Int)) = s
  induction l generalizing s with
  | nil => simp [loop]; rfl
  | cons m l ih =>
    have := ih (arrive s.1 m % 100,
      if crosses s.1 m then s.2 + (m.steps : Int) / 100 + 1 else s.2 + (m.steps : Int) / 100)
    simp [List.forIn_cons, loop, crosses, arrive] at this ⊢
    by_cases hd : m.dir = 'R' <;> simp only [hd, ite_true, ite_false] at this ⊢ <;>
      split at this <;> split <;> first | exact this | (exfalso; omega)

theorem part2_correct (ms : Array Move) : part2 ms = spec ms := by
  rw [part2_eq_loop, loop_eq 50 0 ms.toList (by omega), spec]; simp

end Examples2025.Day01Part2Verified
