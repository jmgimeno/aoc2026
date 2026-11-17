import Aoc2026.Util.MaxHeap

/-!
Proofs about `MaxHeap` for any type with a lawful order, generalizing `MaxHeapVerified.lean`,
which proves the same for `Nat`. The two files follow the same steps, so they can be compared
side by side.

The order is `compare`, required to be transitive and antisymmetric through `Std.TransOrd`.
Instead of `≤` on `Nat`, the proofs use `Le a b`, which means `(compare a b).isLE = true`. The
reasoning about values, which `omega` did for `Nat`, becomes explicit calls to order lemmas.
The reasoning about positions is still done by `omega`.

`val` needs a default value for positions outside the array, so the theorems from step 4 on
also require `[Inhabited α]`.

A structure with `deriving Ord` does not get `Std.TransOrd` automatically.
-/

namespace Aoc2026.MaxHeap.Ord

variable {α : Type} [Ord α]

/-! ## The order -/

/-- `a` is at most `b` according to `compare`. -/
def Le (a b : α) : Prop := (compare a b).isLE = true

theorem le_refl [Std.TransOrd α] (a : α) : Le a a := Std.ReflCmp.isLE_rfl

theorem le_trans [Std.TransOrd α] {a b c : α} (h1 : Le a b) (h2 : Le b c) : Le a c :=
  Std.TransCmp.isLE_trans h1 h2

theorem le_of_lt {a b : α} (h : compare a b = .lt) : Le a b := Ordering.isLE_of_eq_lt h

/-- How the code tests "not smaller": `!(compare a b).isLT` means `b ≤ a`. -/
theorem not_isLT_iff [Std.TransOrd α] (a b : α) :
    (!(compare a b).isLT) = true ↔ Le b a := by
  rw [Le, ← Std.OrientedCmp.isGE_iff_isLE]
  cases compare a b <;> rfl

theorem isLT_iff (a b : α) : (compare a b).isLT = true ↔ compare a b = .lt :=
  Ordering.isLT_iff_eq_lt


/-! ## 1. The heap property -/

theorem parent_bounds {i : Nat} (h : 1 < i) : 1 ≤ parent i ∧ parent i < i := by
  simp only [parent]; omega

/-- No element is larger than its parent. Positions start at 1, as in `MaxHeap`. -/
def IsHeap (data : Array α) : Prop :=
  ∀ i (h1 : 1 < i) (h2 : i ≤ data.size),
    Le data[i - 1] (data[parent i - 1]'(by have := parent_bounds h1; omega))

/-- The executable check and the logical definition agree. -/
theorem isHeap_iff [Std.TransOrd α] (data : Array α) :
    (⟨data⟩ : MaxHeap α).isHeap = true ↔ IsHeap data := by
  simp only [isHeap, size, IsHeap, List.all_eq_true, List.mem_range]
  constructor
  · intro H i h1 h2
    have hp := parent_bounds h1
    have := H (i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega, show (i == 1) = false by simp; omega, Bool.false_or,
      getElem?_pos data (parent i - 1) (by omega), getElem?_pos data (i - 1) (by omega)] at this
    exact (not_isLT_iff _ _).1 this
  · intro H k hk
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hp := parent_bounds (i := k + 1) (by omega)
      rw [show k + 1 - 1 = k by omega, show (k + 1 == 1) = false by simp; omega, Bool.false_or,
        getElem?_pos data (parent (k + 1) - 1) (by omega), getElem?_pos data k (by omega)]
      exact (not_isLT_iff _ _).2 (H (k + 1) (by omega) (by omega))

instance [Std.TransOrd α] (data : Array α) : Decidable (IsHeap data) :=
  decidable_of_iff _ (isHeap_iff data)

/-! The examples are decided by running `isHeap`. -/

example : IsHeap #[9, 6, 5, 4, 1, 3, 2, 1] := by decide
example : ¬ IsHeap #[1, 5] := by decide
example : IsHeap (#[] : Array Nat) := by decide
example : IsHeap #["c", "b", "a"] := by decide

/-! ## 2. The elements are kept -/

omit [Ord α] in
/-- A swap only reorders. The library proves it for `swap`, which needs bounds proofs. -/
theorem swapIfInBounds_perm (a : Array α) (i j : Nat) :
    (a.swapIfInBounds i j).toList.Perm a.toList := by
  unfold Array.swapIfInBounds
  split
  · split
    · exact (Array.swap_perm ..).toList
    · exact List.Perm.refl _
  · exact List.Perm.refl _

/-- `fun_induction` gives one case per branch of `heapUp`, with the induction hypothesis for
the recursive call. -/
theorem heapUp_perm (data : Array α) (i : Nat) : (heapUp data i).toList.Perm data.toList := by
  fun_induction heapUp data i with
  | case1 data i _ p _ _ ih => exact ih.trans (swapIfInBounds_perm ..)
  | case2 => exact List.Perm.refl _
  | case3 => exact List.Perm.refl _

theorem heapDown_perm (data : Array α) (i : Nat) :
    (heapDown data i).toList.Perm data.toList := by
  fun_induction heapDown data i with
  | case1 data i _ _ _ _ c _ _ _ ih => exact ih.trans (swapIfInBounds_perm ..)
  | case2 => exact List.Perm.refl _
  | case3 => exact List.Perm.refl _

/-- `push` adds exactly `x`. -/
theorem push_perm (h : MaxHeap α) (x : α) :
    (h.push x).data.toList.Perm (h.data.toList ++ [x]) := by
  simp only [push]
  simpa using heapUp_perm (h.data.push x) (h.data.size + 1)

theorem heapify_go_perm (data : Array α) (n : Nat) :
    (heapify.go data n).toList.Perm data.toList := by
  induction n generalizing data with
  | zero => exact List.Perm.refl _
  | succ n ih => exact (ih _).trans (heapDown_perm ..)

/-- `heapify` keeps the same elements. -/
theorem heapify_perm (data : Array α) : (heapify data).data.toList.Perm data.toList :=
  heapify_go_perm ..

omit [Ord α] in
/-- Replacing the root by the last element and dropping the last one loses only the root. -/
theorem replaceRoot_perm (data : Array α) (hne : 0 < data.size) :
    data.toList.Perm (data[0] :: (data.pop.setIfInBounds 0 data[data.size - 1]).toList) := by
  rcases data with ⟨_ | ⟨a, rest⟩⟩
  · simp at hne
  · rcases List.eq_nil_or_concat rest with rfl | ⟨mid, last, rfl⟩
    · simp
    · have e : (a :: (mid ++ [last])).dropLast = a :: mid := by
        rw [← List.cons_append, List.dropLast_concat]
      simp [e]

/-- `pop?` removes exactly the element it returns. -/
theorem pop?_perm (h : MaxHeap α) (x : α) (h' : MaxHeap α) (hp : h.pop? = some (x, h')) :
    h.data.toList.Perm (x :: h'.data.toList) := by
  simp only [pop?] at hp
  split at hp
  · rename_i hne
    simp only [Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact (replaceRoot_perm h.data hne).trans (List.Perm.cons _ (heapDown_perm ..).symm)
  · simp at hp

/-! ## 3. The root is the maximum -/

/-- Every position is below the root: follow the parents up, by strong induction. -/
theorem root_max_pos [Std.TransOrd α] (data : Array α) (h : IsHeap data) (i : Nat)
    (h1 : 1 ≤ i) (h2 : i ≤ data.size) : Le data[i - 1] data[0] := by
  induction i using Nat.strongRecOn with
  | _ i ih =>
    by_cases hi : i = 1
    · subst hi; exact le_refl _
    · have hp := parent_bounds (i := i) (by omega)
      exact le_trans (h i (by omega) h2) (ih (parent i) hp.2 hp.1 (by omega))

/-- The same, with 0-based indices. -/
theorem root_max [Std.TransOrd α] (data : Array α) (h : IsHeap data) (k : Nat)
    (hk : k < data.size) : Le data[k] data[0] := by
  simpa using root_max_pos data h (k + 1) (by omega) (by omega)

/-- `max?` returns an element that no element of the heap exceeds. -/
theorem max?_max [Std.TransOrd α] (h : MaxHeap α) (hh : IsHeap h.data) (m : α)
    (hm : h.max? = some m) (y : α) (hy : y ∈ h.data) : Le y m := by
  simp only [max?] at hm
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hy
  have h0 : 0 < h.data.size := by omega
  rw [getElem?_pos h.data 0 h0, Option.some.injEq] at hm
  subst hm
  exact root_max h.data hh k hk

/-- `pop?` returns an element that no element left in the heap exceeds. -/
theorem pop?_max [Std.TransOrd α] (h : MaxHeap α) (hh : IsHeap h.data) (x : α)
    (h' : MaxHeap α) (hp : h.pop? = some (x, h')) (y : α) (hy : y ∈ h'.data) : Le y x := by
  have hm : h.max? = some x := by
    simp only [pop?] at hp
    split at hp
    · rename_i hne
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      simp [max?, getElem?_pos h.data 0 hne, hp.1]
    · simp at hp
  have hmem : y ∈ h.data.toList :=
    (pop?_perm h x h' hp).symm.subset (List.mem_cons_of_mem _ (by simpa using hy))
  exact max?_max h hh x hm y (by simpa using hmem)

/-! ## 4. `push` keeps the heap property -/

/-- The value at position `k`, with no bounds proof. `default` outside the array. -/
def val [Inhabited α] (data : Array α) (k : Nat) : α := data.getD (k - 1) default

omit [Ord α] in
theorem val_eq [Inhabited α] (data : Array α) (k : Nat) (h : k - 1 < data.size) :
    val data k = data[k - 1] := by
  simp [val, Array.getD, h]

/-- The heap property, stated with `val`. -/
def IsHeapV [Inhabited α] (data : Array α) : Prop :=
  ∀ k, 1 < k → k ≤ data.size → Le (val data k) (val data (parent k))

theorem isHeap_iff_val [Inhabited α] (data : Array α) : IsHeap data ↔ IsHeapV data := by
  constructor
  · intro h k h1 h2
    have hp := parent_bounds h1
    rw [val_eq data k (by omega), val_eq data (parent k) (by omega)]
    exact h k h1 h2
  · intro h k h1 h2
    have hp := parent_bounds h1
    have := h k h1 h2
    rwa [val_eq data k (by omega), val_eq data (parent k) (by omega)] at this

omit [Ord α] in
/-- Swapping positions `p` and `i`, both in the array. -/
theorem val_swap [Inhabited α] (data : Array α) (p i k : Nat) (hp : 1 ≤ p ∧ p ≤ data.size)
    (hi : 1 ≤ i ∧ i ≤ data.size) (hk : 1 ≤ k) :
    val (data.swapIfInBounds (p - 1) (i - 1)) k =
      if k = p then val data i else if k = i then val data p else val data k := by
  by_cases hkn : k ≤ data.size
  · rw [val_eq _ k (by simp; omega), Array.getElem_swapIfInBounds]
    by_cases h1 : k = p
    · rw [dite_eq_left ⟨by omega, by omega⟩, ite_eq_left h1, val_eq data i (by omega)]
    · by_cases h2 : k = i
      · rw [dite_eq_right (by omega), dite_eq_left ⟨by omega, by omega⟩, ite_eq_right h1, ite_eq_left h2,
          val_eq data p (by omega)]
      · rw [dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_right h1, ite_eq_right h2,
          val_eq data k (by omega)]
  · have e1 : val (data.swapIfInBounds (p - 1) (i - 1)) k = default := by
      simp [val, Array.getD]; omega
    have e2 : val data k = default := by simp [val, Array.getD]; omega
    rw [e1, e2]
    have : k ≠ p := by omega
    have : k ≠ i := by omega
    simp [*]

omit [Ord α] in
/-- Pushing `x` puts it at position `size + 1`. -/
theorem val_push [Inhabited α] (data : Array α) (x : α) (k : Nat) (hk : 1 ≤ k) (hkn : k ≤ data.size + 1) :
    val (data.push x) k = if k = data.size + 1 then x else val data k := by
  rw [val_eq _ k (by simp; omega), Array.getElem_push]
  by_cases h : k = data.size + 1
  · simp [h]
  · simp [h, show k - 1 < data.size by omega, val_eq data k (by omega)]

theorem le_of_not_isLT [Std.TransOrd α] {a b : α} (h : ¬ (compare a b).isLT = true) : Le b a :=
  (not_isLT_iff a b).1 (by revert h; cases compare a b <;> simp [Ordering.isLT])

/-- What holds while `heapUp` moves the element at position `i` up:

1. Every position other than `i` is at most its parent. Only `i` may be too large.
2. The children of `i` are at most the parent of `i`, so that after swapping `i` with its
  parent, the old parent is still large enough for them. -/
def UpInv [Inhabited α] (data : Array α) (i : Nat) : Prop :=
  (∀ k, 1 < k → k ≤ data.size → k ≠ i → Le (val data k) (val data (parent k))) ∧
  (∀ k, 1 < k → k ≤ data.size → parent k = i → 1 < i →
    Le (val data k) (val data (parent i)))

theorem heapUp_isHeapV [Std.TransOrd α] [Inhabited α] (data : Array α) (i : Nat) (hi : 1 ≤ i ∧ i ≤ data.size)
    (hinv : UpInv data i) : IsHeapV (heapUp data i) := by
  fun_induction heapUp data i with
  | case1 data i h p hp hlt ih =>
    have hlt' : compare (val data p) (val data i) = .lt := by
      rwa [isLT_iff, ← val_eq data p (by omega), ← val_eq data i (by omega)] at hlt
    have hp' : p = parent i := rfl
    obtain ⟨A, B⟩ := hinv
    apply ih
    · simp; omega
    constructor
    · -- every position other than `p` is at most its parent
      intro k h1 h2 hkp
      simp only [Array.size_swapIfInBounds] at h2
      have hk := parent_bounds h1
      rw [val_swap data p i k ⟨hp.1, by omega⟩ ⟨by omega, hi.2⟩ (by omega),
        val_swap data p i (parent k) ⟨hp.1, by omega⟩ ⟨by omega, hi.2⟩ (by omega),
        ite_eq_right hkp]
      by_cases hki : k = i
      · -- the element that moved down, below the one that moved up
        rw [ite_eq_left hki, ite_eq_left (show parent k = p by rw [hki])]
        exact le_of_lt hlt'
      · rw [ite_eq_right hki]
        by_cases hpk1 : parent k = p
        · -- a sibling of `i`: below the old parent, so below the new one
          rw [ite_eq_left hpk1]
          have := A k h1 h2 hki
          rw [hpk1] at this
          exact le_trans this (le_of_lt hlt')
        · rw [ite_eq_right hpk1]
          by_cases hpk2 : parent k = i
          · -- a child of `i`: the second part of the invariant
            rw [ite_eq_left hpk2]
            have := B k h1 h2 hpk2 h.1
            rw [← hp'] at this
            exact this
          · rw [ite_eq_right hpk2]
            exact A k h1 h2 hki
    · -- the children of `p` are at most the parent of `p`
      intro k h1 h2 hpk hp1
      simp only [Array.size_swapIfInBounds] at h2
      have hk := parent_bounds h1
      have hpp := parent_bounds hp1
      have Ap := A p hp1 (by omega) (by omega)
      rw [val_swap data p i k ⟨hp.1, by omega⟩ ⟨by omega, hi.2⟩ (by omega),
        val_swap data p i (parent p) ⟨hp.1, by omega⟩ ⟨by omega, hi.2⟩ (by omega),
        ite_eq_right (show parent p ≠ p by omega), ite_eq_right (show parent p ≠ i by omega),
        ite_eq_right (show k ≠ p by omega)]
      by_cases hki : k = i
      · rw [ite_eq_left hki]
        exact Ap
      · rw [ite_eq_right hki]
        have := A k h1 h2 hki
        rw [hpk] at this
        exact le_trans this Ap
  | case2 data i h p hp hnlt =>
    rw [← val_eq data p (by omega), ← val_eq data i (by omega)] at hnlt
    intro k h1 h2
    by_cases hki : k = i
    · rw [hki]
      show Le (val data i) (val data p)
      exact le_of_not_isLT hnlt
    · exact hinv.1 k h1 h2 hki
  | case3 data i h =>
    intro k h1 h2
    exact hinv.1 k h1 h2 (by omega)

/-- After appending, the invariant holds at the new last position: the rest was a heap, and
the new position has no children yet. -/
theorem upInv_push [Inhabited α] (data : Array α) (x : α) (hh : IsHeapV data) :
    UpInv (data.push x) (data.size + 1) := by
  constructor
  · intro k h1 h2 hkn
    simp only [Array.size_push] at h2
    have hk := parent_bounds h1
    rw [val_push data x k (by omega) h2, val_push data x (parent k) (by omega) (by omega),
      ite_eq_right hkn, ite_eq_right (show parent k ≠ data.size + 1 by omega)]
    exact hh k h1 (by omega)
  · intro k h1 h2 hpk _
    simp only [Array.size_push] at h2
    simp only [parent] at hpk
    omega

/-- `push` keeps the heap property. -/
theorem push_isHeap [Std.TransOrd α] [Inhabited α] (h : MaxHeap α) (x : α) (hh : IsHeap h.data) :
    IsHeap (h.push x).data := by
  rw [isHeap_iff_val] at hh ⊢
  simp only [push]
  exact heapUp_isHeapV _ _ (by simp) (upInv_push h.data x hh)

/-- Every heap built from `{}` with `push` is a heap. -/
theorem pushAll_isHeap [Std.TransOrd α] [Inhabited α] (xs : List α) :
    IsHeap (xs.foldl MaxHeap.push {}).data := by
  suffices ∀ h : MaxHeap α, IsHeap h.data → IsHeap (xs.foldl MaxHeap.push h).data from
    this {} (fun i h1 h2 => by simp [EmptyCollection.emptyCollection, empty] at h2; omega)
  induction xs with
  | nil => intro h hh; exact hh
  | cons x xs ih => intro h hh; exact ih _ (push_isHeap h x hh)

/-! ## 5. `pop?` keeps the heap property -/

/-- The heap property restricted to the edges whose parent is at position `m` or later. With
`m = 1` it is the whole heap property. `heapify` needs the general form, because at each step
only the subtrees from some position on are heaps. -/
def HeapFrom [Inhabited α] (data : Array α) (m : Nat) : Prop :=
  ∀ k, 1 < k → k ≤ data.size → m ≤ parent k → Le (val data k) (val data (parent k))

theorem heapFrom_one_iff [Inhabited α] (data : Array α) : HeapFrom data 1 ↔ IsHeapV data := by
  constructor
  · intro h k h1 h2
    exact h k h1 h2 (parent_bounds h1).1
  · intro h k h1 h2 _
    exact h k h1 h2

/-- What holds while `heapDown` moves the element at position `i` down, for the edges whose
parent is at position `m` or later:

1. Every position whose parent is not `i` is at most its parent. Only the edges from `i` to
  its children may be broken.
2. The children of `i` are at most the parent of `i`, so that the larger child still fits
  there after moving up to `i`. -/
def DownInv [Inhabited α] (data : Array α) (m i : Nat) : Prop :=
  (∀ k, 1 < k → k ≤ data.size → m ≤ parent k → parent k ≠ i →
    Le (val data k) (val data (parent k))) ∧
  (∀ k, 1 < k → k ≤ data.size → parent k = i → 1 < i → m ≤ parent i →
    Le (val data k) (val data (parent i)))

theorem heapDown_heapFrom [Std.TransOrd α] [Inhabited α] (data : Array α) (m i : Nat) (hi : 1 ≤ i) (hm : m ≤ i)
    (hinv : DownInv data m i) : HeapFrom (heapDown data i) m := by
  fun_induction heapDown data i with
  | case1 data i l r h hl c hc hx hlt ih =>
    have hchild : parent c = i ∧
        ∀ k, 1 < k → k ≤ data.size → parent k = i → Le (val data k) (val data c) := by
      have hlr : ∀ k, 1 < k → parent k = i → k = l ∨ k = r := by
        intro k _ hpk
        simp only [l, r, left, right, parent] at *
        omega
      split at hx
      · rename_i hr
        split at hx
        · -- the right child is larger
          rename_i hcmp
          have hcr : c = r := by simp at hx; omega
          have hcmp : compare (val data l) (val data r) = .lt := by
            rw [isLT_iff] at hcmp
            rw [val_eq data l (by omega), val_eq data r (by omega)]
            exact hcmp
          refine ⟨by simp only [hcr, r, right, parent]; omega, ?_⟩
          intro k h1 _ hpk
          rcases hlr k h1 hpk with rfl | rfl
          · rw [hcr]; exact le_of_lt hcmp
          · rw [hcr]; exact le_refl _
        · -- the left child is at least as large
          rename_i hcmp
          have hcl : c = l := by simp at hx; omega
          have hcmp : Le (val data r) (val data l) := by
            rw [val_eq data l (by omega), val_eq data r (by omega)]
            exact le_of_not_isLT hcmp
          refine ⟨by simp only [hcl, l, left, parent]; omega, ?_⟩
          intro k h1 _ hpk
          rcases hlr k h1 hpk with rfl | rfl
          · rw [hcl]; exact le_refl _
          · rw [hcl]; exact hcmp
      · -- there is no right child
        rename_i hr
        have hcl : c = l := by simp at hx; omega
        refine ⟨by simp only [hcl, l, left, parent]; omega, ?_⟩
        intro k h1 h2 hpk
        rcases hlr k h1 hpk with rfl | rfl
        · rw [hcl]; exact le_refl _
        · omega
    rw [isLT_iff, ← val_eq data i (by omega), ← val_eq data c (by omega)] at hlt
    obtain ⟨A, B⟩ := hinv
    apply ih (by omega) (by omega)
    constructor
    · -- every position whose parent is not `c` is at most its parent
      intro k h1 h2 hmk hpkc
      simp only [Array.size_swapIfInBounds] at h2
      have hk := parent_bounds h1
      rw [val_swap data i c k ⟨hi, by omega⟩ ⟨by omega, hc.2⟩ (by omega),
        val_swap data i c (parent k) ⟨hi, by omega⟩ ⟨by omega, hc.2⟩ (by omega)]
      by_cases hki : k = i
      · -- the larger child, now at `i`: below the parent of `i` by the second part
        rw [ite_eq_left hki, ite_eq_right (show parent k ≠ i by omega),
          ite_eq_right (show parent k ≠ c by omega)]
        rw [hki] at hmk ⊢
        exact B c (by omega) hc.2 hchild.1 (by omega) hmk
      · rw [ite_eq_right hki]
        by_cases hkc : k = c
        · -- the element that moved down, below the larger child that moved up
          rw [ite_eq_left hkc, ite_eq_left (show parent k = i by rw [hkc]; exact hchild.1)]
          exact le_of_lt hlt
        · rw [ite_eq_right hkc]
          by_cases hpki : parent k = i
          · -- the other child of `i`: below the larger one
            rw [ite_eq_left hpki]
            exact hchild.2 k h1 h2 hpki
          · rw [ite_eq_right hpki, ite_eq_right hpkc]
            exact A k h1 h2 hmk hpki
    · -- the children of `c` are at most the parent of `c`, which is now the larger child
      intro k h1 h2 hpk _ _
      simp only [Array.size_swapIfInBounds] at h2
      have hk := parent_bounds h1
      rw [val_swap data i c k ⟨hi, by omega⟩ ⟨by omega, hc.2⟩ (by omega),
        val_swap data i c (parent c) ⟨hi, by omega⟩ ⟨by omega, hc.2⟩ (by omega),
        ite_eq_right (show k ≠ i by omega), ite_eq_right (show k ≠ c by omega),
        ite_eq_left hchild.1]
      have := A k h1 h2 (by omega) (by omega)
      rw [hpk] at this
      exact this
  | case2 data i l r h hl c hc hx hnlt =>
    have hchild : parent c = i ∧
        ∀ k, 1 < k → k ≤ data.size → parent k = i → Le (val data k) (val data c) := by
      have hlr : ∀ k, 1 < k → parent k = i → k = l ∨ k = r := by
        intro k _ hpk
        simp only [l, r, left, right, parent] at *
        omega
      split at hx
      · rename_i hr
        split at hx
        · -- the right child is larger
          rename_i hcmp
          have hcr : c = r := by simp at hx; omega
          have hcmp : compare (val data l) (val data r) = .lt := by
            rw [isLT_iff] at hcmp
            rw [val_eq data l (by omega), val_eq data r (by omega)]
            exact hcmp
          refine ⟨by simp only [hcr, r, right, parent]; omega, ?_⟩
          intro k h1 _ hpk
          rcases hlr k h1 hpk with rfl | rfl
          · rw [hcr]; exact le_of_lt hcmp
          · rw [hcr]; exact le_refl _
        · -- the left child is at least as large
          rename_i hcmp
          have hcl : c = l := by simp at hx; omega
          have hcmp : Le (val data r) (val data l) := by
            rw [val_eq data l (by omega), val_eq data r (by omega)]
            exact le_of_not_isLT hcmp
          refine ⟨by simp only [hcl, l, left, parent]; omega, ?_⟩
          intro k h1 _ hpk
          rcases hlr k h1 hpk with rfl | rfl
          · rw [hcl]; exact le_refl _
          · rw [hcl]; exact hcmp
      · -- there is no right child
        rename_i hr
        have hcl : c = l := by simp at hx; omega
        refine ⟨by simp only [hcl, l, left, parent]; omega, ?_⟩
        intro k h1 h2 hpk
        rcases hlr k h1 hpk with rfl | rfl
        · rw [hcl]; exact le_refl _
        · omega
    rw [← val_eq data i (by omega), ← val_eq data c (by omega)] at hnlt
    have hci := le_of_not_isLT hnlt
    intro k h1 h2 hmk
    by_cases hpk : parent k = i
    · have := hchild.2 k h1 h2 hpk
      rw [hpk]
      exact le_trans this hci
    · exact hinv.1 k h1 h2 hmk hpk
  | case3 data i l h =>
    intro k h1 h2 hmk
    have hk := parent_bounds h1
    apply hinv.1 k h1 h2 hmk
    simp only [l, left, parent] at *
    omega

omit [Ord α] in
/-- Replacing the root and dropping the last element leaves the other positions unchanged. -/
theorem val_replaceRoot [Inhabited α] (data : Array α) (v : α) (k : Nat) (hk : 2 ≤ k) (hkn : k + 1 ≤ data.size) :
    val (data.pop.setIfInBounds 0 v) k = val data k := by
  rw [val_eq _ k (by simp; omega), val_eq data k (by omega)]
  rw [Array.getElem_setIfInBounds (by simp; omega), ite_eq_right (show 0 ≠ k - 1 by omega),
    Array.getElem_pop]

/-- `pop?` keeps the heap property. -/
theorem pop?_isHeap [Std.TransOrd α] [Inhabited α] (h : MaxHeap α) (hh : IsHeap h.data) (x : α) (h' : MaxHeap α)
    (hp : h.pop? = some (x, h')) : IsHeap h'.data := by
  simp only [pop?] at hp
  split at hp
  · simp only [Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨-, rfl⟩ := hp
    rw [isHeap_iff_val] at hh ⊢
    rw [← heapFrom_one_iff]
    apply heapDown_heapFrom _ 1 1 (Nat.le_refl _) (Nat.le_refl _)
    constructor
    · intro k h1 h2 _ hpk
      simp only [Array.size_setIfInBounds, Array.size_pop] at h2
      have hk := parent_bounds h1
      rw [val_replaceRoot h.data _ k (by omega) (by omega),
        val_replaceRoot h.data _ (parent k) (by omega) (by omega)]
      exact hh k h1 (by omega)
    · intro k _ _ _ h1 _
      omega
  · simp at hp

/-! ## 6. `heapify` builds a heap -/

/-- `heapify.go data j` calls `heapDown` on positions `j`, ..., `1`. Before it starts, the
subtrees from position `j + 1` on must already be heaps. -/
theorem heapify_go_heapFrom [Std.TransOrd α] [Inhabited α] (data : Array α) (j : Nat) (h : HeapFrom data (j + 1)) :
    IsHeapV (heapify.go data j) := by
  induction j generalizing data with
  | zero => exact (heapFrom_one_iff data).1 h
  | succ j ih =>
    apply ih
    apply heapDown_heapFrom data (j + 1) (j + 1) (by omega) (Nat.le_refl _)
    constructor
    · intro k h1 h2 hmk hpk
      exact h k h1 h2 (by omega)
    · intro k _ _ _ hi1 hm
      have := parent_bounds hi1
      omega

/-- `heapify` builds a heap from any array. Positions after `size / 2` have no children, so
the subtrees from `size / 2 + 1` on are heaps from the start. -/
theorem heapify_isHeap [Std.TransOrd α] [Inhabited α] (data : Array α) : IsHeap (heapify data).data := by
  rw [isHeap_iff_val]
  apply heapify_go_heapFrom
  intro k h1 h2 hmk
  simp only [parent] at hmk
  omega

/-! The theorems apply to any type with a lawful order, such as `Nat` or `String`. -/

example (xs : List Nat) : IsHeap (xs.foldl MaxHeap.push {}).data := pushAll_isHeap xs
example (data : Array String) : IsHeap (heapify data).data := heapify_isHeap data

end Aoc2026.MaxHeap.Ord
