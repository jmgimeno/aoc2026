namespace Examples2025.Day05Verified

abbrev Rng := Nat × Nat
def covers (rs : List Rng) (x : Nat) : Prop := ∃ r ∈ rs, r.1 ≤ x ∧ x ≤ r.2

def add (acc : List Rng) (r : Rng) : List Rng :=
  match acc with
  | [] => [r]
  | l :: t => if r.1 ≤ l.2 then (l.1, max l.2 r.2) :: t else r :: l :: t

def merge (rs : List Rng) : List Rng := (rs.foldl add []).reverse

#eval merge [(1,3),(2,5),(7,8)]
#eval merge [(5,6),(1,2)]   -- unsorted input loses 1 and 2!

theorem covers_cons (r : Rng) (t : List Rng) (x : Nat) :
    covers (r :: t) x ↔ (r.1 ≤ x ∧ x ≤ r.2) ∨ covers t x := by
  simp [covers]

theorem covers_add (acc : List Rng) (r : Rng) (x : Nat)
    (h : ∀ l ∈ acc.head?, l.1 ≤ r.1) :
    covers (add acc r) x ↔ covers acc x ∨ (r.1 ≤ x ∧ x ≤ r.2) := by
  cases acc with
  | nil => simp [add, covers]
  | cons l t =>
    have hl : l.1 ≤ r.1 := h l (by simp)
    by_cases hc : covers t x <;> by_cases hr : r.1 ≤ l.2 <;>
      simp only [add, hr, ite_true, ite_false, covers_cons, hc] <;> simp <;> omega

theorem head_add (acc : List Rng) (r : Rng) (k : Nat)
    (hr : r.1 ≤ k) (h : ∀ l ∈ acc.head?, l.1 ≤ k) :
    ∀ l ∈ (add acc r).head?, l.1 ≤ k := by
  cases acc with
  | nil => simpa [add]
  | cons l t =>
    have hl : l.1 ≤ k := h l (by simp)
    by_cases hc : r.1 ≤ l.2 <;> simp [add, hc] <;> omega

theorem covers_foldl (rs acc : List Rng) (x : Nat)
    (hs : rs.Pairwise (fun a b => a.1 ≤ b.1))
    (h : ∀ l ∈ acc.head?, ∀ r ∈ rs, l.1 ≤ r.1) :
    covers (rs.foldl add acc) x ↔ covers acc x ∨ covers rs x := by
  induction rs generalizing acc with
  | nil => simp [covers]
  | cons r rs ih =>
    have ⟨hr, hs'⟩ := List.pairwise_cons.1 hs
    have hh : ∀ l ∈ (add acc r).head?, ∀ s ∈ rs, l.1 ≤ s.1 := by
      intro l hl s hmem
      exact head_add acc r s.1 (hr s hmem) (fun l' hl' => h l' hl' s (by simp [hmem])) l hl
    rw [List.foldl_cons, ih _ hs' hh, covers_add _ _ _ (fun l hl => h l hl r (by simp)),
      covers_cons]
    exact or_assoc

/-- Merging neither adds nor removes points, provided the input is sorted. -/
theorem merge_correct (rs : List Rng) (x : Nat)
    (hs : rs.Pairwise (fun a b => a.1 ≤ b.1)) :
    covers (merge rs) x ↔ covers rs x := by
  have := covers_foldl rs [] x hs (by simp)
  simpa [merge, covers] using this

end Examples2025.Day05Verified
