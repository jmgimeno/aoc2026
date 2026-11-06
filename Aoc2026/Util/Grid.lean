/-!
Two-dimensional grids stored in a flat `Array`, with `(0, 0)` at the top left and `y`
growing downwards, the way puzzle inputs are read.

Coordinates are `Int`, not `Nat`: stepping off the edge must give a position outside the
grid, whereas in `Nat` the result of `0 - 1` would be `0`, a valid cell.
-/

namespace Aoc2026

structure Pos where
  x : Int
  y : Int
  deriving BEq, Hashable, Ord, Repr, Inhabited

namespace Pos

instance : Add Pos := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩

instance : ToString Pos := ⟨fun p => s!"({p.x}, {p.y})"⟩

def up : Pos := ⟨0, -1⟩
def right : Pos := ⟨1, 0⟩
def down : Pos := ⟨0, 1⟩
def left : Pos := ⟨-1, 0⟩

/-- The four orthogonal directions, clockwise from `up`. -/
def dirs4 : Array Pos := #[up, right, down, left]

/-- The eight surrounding directions, clockwise from `up`. -/
def dirs8 : Array Pos :=
  #[up, up + right, right, down + right, down, down + left, left, up + left]

/-- Rotates a direction 90° clockwise. -/
def turnRight (d : Pos) : Pos := ⟨-d.y, d.x⟩

/-- Rotates a direction 90° counterclockwise. -/
def turnLeft (d : Pos) : Pos := ⟨d.y, -d.x⟩

def manhattan (a b : Pos) : Nat := (a.x - b.x).natAbs + (a.y - b.y).natAbs

end Pos

structure Grid (α : Type) where
  width : Nat
  height : Nat
  cells : Array α
  deriving BEq, Repr

namespace Grid

variable {α β : Type}

def replicate (width height : Nat) (value : α) : Grid α :=
  { width, height, cells := Array.replicate (width * height) value }

/-- Builds a grid from text, one row per line, applying `f` to each character.
All lines must have the same length. -/
def parse (f : Char → α) (input : String) : Except String (Grid α) := do
  let lines := input.lines.toArray.map toString
  let width := (lines[0]?.getD "").length
  let mut cells := Array.emptyWithCapacity (width * lines.size)
  for line in lines, y in [0:lines.size] do
    unless line.length == width do
      throw s!"line {y + 1}: expected {width} columns, got {line.length}"
    for c in line.toList do
      cells := cells.push (f c)
  return { width, height := lines.size, cells }

def inBounds (g : Grid α) (p : Pos) : Bool :=
  0 ≤ p.x && p.x < g.width && 0 ≤ p.y && p.y < g.height

/-- Only meaningful when `p` is in bounds. -/
@[inline] private def index (g : Grid α) (p : Pos) : Nat :=
  (p.y * g.width + p.x).toNat

/-- `none` outside the grid. -/
def get? (g : Grid α) (p : Pos) : Option α :=
  if g.inBounds p then g.cells[g.index p]? else none

/-- `default` outside the grid, which saves checking for the edges. -/
def getD (g : Grid α) (p : Pos) (default : α) : α :=
  (g.get? p).getD default

/-- Writing outside the grid does nothing. It updates in place when `g` is not shared, so
avoid keeping the old grid around in a loop, or every write copies the whole array. -/
def set (g : Grid α) (p : Pos) (value : α) : Grid α :=
  if g.inBounds p then
    { g with cells := g.cells.setIfInBounds (g.index p) value }
  else
    g

/-- Like `set`, computing the new value from the current one. -/
def modify (g : Grid α) (p : Pos) (f : α → α) : Grid α :=
  if g.inBounds p then
    { g with cells := g.cells.modify (g.index p) f }
  else
    g

/-- The position of the cell stored at index `i` of `cells`. -/
private def posAt (g : Grid α) (i : Nat) : Pos :=
  ⟨Int.ofNat (i % g.width), Int.ofNat (i / g.width)⟩

/-- All positions, row by row. -/
def positions (g : Grid α) : Array Pos :=
  (Array.range g.cells.size).map g.posAt

/-- The positions at the given offsets from `p` that are inside the grid. -/
def neighbors (g : Grid α) (dirs : Array Pos) (p : Pos) : Array Pos :=
  (dirs.map (p + ·)).filter g.inBounds

def neighbors4 (g : Grid α) (p : Pos) : Array Pos := g.neighbors Pos.dirs4 p

def neighbors8 (g : Grid α) (p : Pos) : Array Pos := g.neighbors Pos.dirs8 p

/-- All positions whose cell satisfies `pred`, row by row. -/
def findAll (g : Grid α) (pred : α → Bool) : Array Pos := Id.run do
  let mut found := #[]
  for cell in g.cells, i in [0:g.cells.size] do
    if pred cell then found := found.push (g.posAt i)
  return found

/-- The first position, row by row, whose cell satisfies `pred`. -/
def find? (g : Grid α) (pred : α → Bool) : Option Pos :=
  (g.cells.findIdx? pred).map g.posAt

def count (g : Grid α) (pred : α → Bool) : Nat :=
  g.cells.countP pred

def map (f : α → β) (g : Grid α) : Grid β :=
  { g with cells := g.cells.map f }

/-- One line per row, for printing a grid while debugging. -/
instance [ToString α] : ToString (Grid α) where
  toString g :=
    let row (y : Nat) := g.cells.extract (y * g.width) ((y + 1) * g.width)
    "\n".intercalate ((List.range g.height).map fun y =>
      String.join ((row y).toList.map toString))

end Grid

/-! ## Tests -/

private def sample : Grid Char :=
  match Grid.parse id "ab\ncd\nef" with
  | .ok g => g
  | .error _ => Grid.replicate 0 0 ' '

#guard sample.width == 2 && sample.height == 3
#guard sample.get? ⟨1, 2⟩ == some 'f'
#guard sample.get? ⟨2, 0⟩ == none
#guard sample.get? ⟨0, -1⟩ == none
#guard sample.getD ⟨-1, 0⟩ '.' == '.'
#guard (sample.set ⟨0, 1⟩ 'X').get? ⟨0, 1⟩ == some 'X'
#guard sample.set ⟨5, 5⟩ 'X' == sample
#guard (sample.modify ⟨1, 0⟩ Char.toUpper).get? ⟨1, 0⟩ == some 'B'
#guard sample.find? (· == 'd') == some ⟨1, 1⟩
#guard sample.findAll (· > 'c') == #[⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩]
#guard sample.count (· < 'c') == 2
#guard sample.positions.size == 6
#guard sample.neighbors4 ⟨0, 0⟩ == #[⟨1, 0⟩, ⟨0, 1⟩]
#guard (sample.neighbors8 ⟨1, 1⟩).size == 5
#guard toString sample == "ab\ncd\nef"
#guard (Grid.parse id "ab\nc").toOption.isNone
#guard (Grid.parse id "").toOption.map (·.cells.size) == some 0
#guard Pos.up.turnRight == Pos.right && Pos.left.turnRight == Pos.up
#guard Pos.up.turnLeft == Pos.left
#guard Pos.manhattan ⟨1, -2⟩ ⟨-3, 4⟩ == 10

end Aoc2026
