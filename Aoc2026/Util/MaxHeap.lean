/-!
A binary max-heap stored in an `Array`.

The tree is implicit in the positions, which are numbered from 1 as in the textbooks: the
root is at position `1`, the children of position `i` are at `2 * i` and `2 * i + 1`, and its
parent is at `i / 2`. The heap property says that no node is smaller than its children, so
the maximum is always at position `1`.

The array itself has no unused slot, because index 0 would need a real value of type `α`.
So position `i` is stored at index `i - 1`. With positions from 1, the parent of the root is
`1 / 2 = 0`, which is outside the heap, so walking up needs no `Nat` subtraction, which would
truncate.

Elements are compared with `Ord`. Tuples have no `Ord` instance on this toolchain, so store a
structure with `deriving Ord` instead: its fields are compared in order, like a tuple.
-/

namespace Aoc2026

structure MaxHeap (α : Type) where
  data : Array α
  deriving Repr

namespace MaxHeap

variable {α : Type}

/-! ### Positions, numbered from 1 -/

def left (i : Nat) : Nat := 2 * i

def right (i : Nat) : Nat := 2 * i + 1

/-- `0` for the root, which is not a position of the heap. -/
def parent (i : Nat) : Nat := i / 2

/-! ### Basic operations -/

def empty : MaxHeap α := ⟨#[]⟩

/-- Lets you write `{}` for an empty heap. -/
instance : EmptyCollection (MaxHeap α) := ⟨empty⟩

def size (h : MaxHeap α) : Nat := h.data.size

def isEmpty (h : MaxHeap α) : Bool := h.data.isEmpty

/-- The largest element, without removing it. Position 1 is stored at index 0. -/
def max? (h : MaxHeap α) : Option α := h.data[0]?

/-! ### Insertion -/

/-- Moves the element at position `i` up while its parent is smaller, swapping them. Does
nothing if `i` is not a position of `data` other than the root.

The dependent `if h :` gives a proof of the bounds, and `hp` adds what `parent` computes, so
Lean proves both indices valid without `Option`. The recursion stops because the position
halves on each call, which Lean checks with `termination_by` and `decreasing_by`.

Internal: use `push`. It is not `private` only so that `MaxHeapVerified.lean` can prove
things about it. -/
def heapUp [Ord α] (data : Array α) (i : Nat) : Array α :=
  if h : 1 < i ∧ i ≤ data.size then
    let p := parent i
    have hp : 1 ≤ p ∧ p < i := by simp only [p, parent]; omega
    if (compare data[p - 1] data[i - 1]).isLT then
      heapUp (data.swapIfInBounds (p - 1) (i - 1)) p
    else
      data
  else
    data
termination_by i
decreasing_by omega

/-- Appends `x` at the end and moves it up to its place.

Read the size before pushing: in `heapUp (h.data.push x) (h.data.size + 1)`, `h` is still in
use when the array is pushed, so `push` copies the whole array, and inserting `n` elements
becomes quadratic. -/
def push [Ord α] (h : MaxHeap α) (x : α) : MaxHeap α :=
  let i := h.data.size + 1
  ⟨heapUp (h.data.push x) i⟩

/-! ### Removal -/

/-- Moves the element at position `i` down while a child is larger, swapping it with the
larger child. Does nothing if `i` is not a position of `data` with children.

The larger child is chosen together with a proof that it is a valid position below `i`, as a
subtype `{c // ...}`. That way `c` is a plain variable, and `decreasing_by` can use the proof
to show that `data.size - i` decreases.

Internal: use `pop?` or `heapify`. It is not `private` only so that `MaxHeapVerified.lean`
can prove things about it. -/
def heapDown [Ord α] (data : Array α) (i : Nat) : Array α :=
  let l := left i
  let r := right i
  if h : 1 ≤ i ∧ l ≤ data.size then
    have hl : i < l ∧ l < r := by simp only [l, r, MaxHeap.left, MaxHeap.right]; omega
    let ⟨c, hc⟩ : { c // i < c ∧ c ≤ data.size } :=
      if hr : r ≤ data.size then
        if (compare data[l - 1] data[r - 1]).isLT then ⟨r, by omega⟩ else ⟨l, by omega⟩
      else
        ⟨l, by omega⟩
    if (compare data[i - 1] data[c - 1]).isLT then
      heapDown (data.swapIfInBounds (i - 1) (c - 1)) c
    else
      data
  else
    data
termination_by data.size - i
decreasing_by simp only [Array.size_swapIfInBounds]; omega

/-- Removes the largest element, returning it with the new heap, or `none` if it is empty.

The last element replaces the root and moves down to its place.

When you call it, do not mention the old heap after `pop?`, not even in the `none` branch:
`match h.pop? with | some (x, h') => ... | none => (s, h)` keeps `h` alive, so the array is
shared and every call copies it. Write `| none => (s, {})` instead. -/
def pop? [Ord α] (h : MaxHeap α) : Option (α × MaxHeap α) :=
  let data := h.data
  if hne : 0 < data.size then
    let top := data[0]
    let last := data[data.size - 1]
    let data := data.pop.setIfInBounds 0 last
    some (top, ⟨heapDown data 1⟩)
  else
    none

/-! ### Construction -/

/-- Reorganizes an array into a heap in `O(n)`, faster than pushing its elements one by one.

Positions after `size / 2` have no children, so they are already heaps. Going backwards from
`size / 2` to `1`, each `heapDown` merges a node with its two children, which are heaps by
then. `go` counts down with structural recursion on `Nat`, so it needs no termination proof. -/
def heapify [Ord α] (data : Array α) : MaxHeap α :=
  let n := data.size / 2
  ⟨go data n⟩
where
  go (data : Array α) : Nat → Array α
    | 0 => data
    | i + 1 => go (heapDown data (i + 1)) i

/-! ### Checks -/

/-- Whether no element is smaller than its children. Meant for tests and debugging. -/
def isHeap [Ord α] (h : MaxHeap α) : Bool :=
  (List.range h.size).all fun k =>
    let i := k + 1
    i == 1 || match h.data[parent i - 1]?, h.data[i - 1]? with
      | some parentValue, some childValue => !(compare parentValue childValue).isLT
      | _, _ => false

end MaxHeap

/-! ## Tests -/

#guard (MaxHeap.empty : MaxHeap Nat).isEmpty
#guard (({} : MaxHeap Nat).max?) == none
#guard MaxHeap.left 1 == 2 && MaxHeap.right 1 == 3
#guard MaxHeap.parent 2 == 1 && MaxHeap.parent 3 == 1
#guard MaxHeap.parent 1 == 0
#guard MaxHeap.parent (MaxHeap.left 5) == 5 && MaxHeap.parent (MaxHeap.right 5) == 5

private def pushAll (xs : List Nat) : MaxHeap Nat := xs.foldl MaxHeap.push {}

#guard (pushAll [3, 1, 4, 1, 5, 9, 2, 6]).data == #[9, 6, 5, 4, 1, 3, 2, 1]
#guard (pushAll [3, 1, 4, 1, 5, 9, 2, 6]).max? == some 9
#guard (pushAll [3, 1, 4, 1, 5, 9, 2, 6]).size == 8
#guard (pushAll [3, 1, 4, 1, 5, 9, 2, 6]).isHeap
#guard (pushAll (List.range 100)).isHeap
#guard !(⟨#[1, 5]⟩ : MaxHeap Nat).isHeap
#guard MaxHeap.heapUp #[1, 2, 3, 9] 4 == #[9, 1, 3, 2]
#guard MaxHeap.heapUp #[1, 2, 3, 9] 1000 == #[1, 2, 3, 9]

/-- Pops at most `n` elements, checking the heap property after each pop. -/
private def popAll (h : MaxHeap Nat) : Nat → Option (List Nat)
  | 0 => some []
  | n + 1 => match h.pop? with
    | none => some []
    | some (x, h') => if h'.isHeap then (x :: ·) <$> popAll h' n else none

#guard popAll (pushAll [3, 1, 4, 1, 5, 9, 2, 6]) 100 == some [9, 6, 5, 4, 3, 2, 1, 1]
#guard popAll (pushAll (List.range 100)) 200 == some (List.range 100).reverse
#guard popAll (pushAll [2, 7]) 1 == some [7]
#guard ({} : MaxHeap Nat).pop?.isNone
#guard (pushAll [7]).pop?.map (fun (x, h) => (x, h.size)) == some (7, 0)
#guard MaxHeap.heapDown #[1, 5, 3] 1 == #[5, 1, 3]
#guard MaxHeap.heapDown #[1, 5, 3] 1000 == #[1, 5, 3]

#guard (MaxHeap.heapify #[3, 1, 4, 1, 5, 9, 2, 6]).isHeap
#guard (MaxHeap.heapify #[3, 1, 4, 1, 5, 9, 2, 6]).size == 8
#guard popAll (MaxHeap.heapify #[3, 1, 4, 1, 5, 9, 2, 6]) 100 == some [9, 6, 5, 4, 3, 2, 1, 1]
#guard (MaxHeap.heapify (Array.range 100)).isHeap
#guard (MaxHeap.heapify (Array.range 100).reverse).isHeap
#guard (MaxHeap.heapify (#[] : Array Nat)).isEmpty
#guard (MaxHeap.heapify #[4]).max? == some 4

end Aoc2026
