import AdventOfCode.Common.Fin
import AdventOfCode.Common.Grid2D
import AdventOfCode.Common.Result
import Std.Data.HashSet

-- Represents natural numbers in the range [1, n).
structure PFin (n: Nat) where
  val: Nat
  is_pos: val ≠ 0
  is_lt: val < n
deriving
  Repr, BEq, ReflBEq,
  LawfulBEq, DecidableEq, Hashable

def PFin.next (x: PFin n): PFin n :=
  let val := x.val + 1
  if h1: val < n then
    ⟨val, (by omega), h1⟩
  else
    have h2: x.val ≠ 0 := x.is_pos
    have h3: 0 < x.val := by omega
    have h4: x.val < n := x.is_lt
    have h5: 1 < n := by omega
    ⟨1, by omega, by omega⟩

def PFin.prev (x: PFin n): PFin n :=
  let val := x.val - 1
  have h1: x.val < n := x.is_lt
  if h2: val = 0 then
    have h3: x.val ≠ 0 := x.is_pos
    have h4: 0 < x.val := by omega
    ⟨n - 1, by omega, by omega⟩
  else ⟨val, h2, by omega⟩

def PFin.tryFrom (x: Fin n): Result (PFin (n - 1)) :=
  if h: x.val ≠ 0 ∧ x.val < n - 1 then Except.ok ⟨x.val, by omega, by omega⟩
  else Except.error "PFin value out of bounds"

structure Blizzard (n m: Nat) where
  row: PFin n
  col: PFin m
deriving
  Repr, BEq, ReflBEq,
  LawfulBEq, DecidableEq, Hashable

structure Storms (n m: Nat) where
  left: Array (Blizzard n m)
  right: Array (Blizzard n m)
  up: Array (Blizzard n m)
  down: Array (Blizzard n m)
deriving
  Repr, BEq, ReflBEq,
  LawfulBEq, DecidableEq, Hashable

def Storms.insertLeft (storms: Storms n m) (row: PFin n) (col: PFin m): Storms n m := {
  left := storms.left.push ⟨row, col⟩
  right := storms.right
  up := storms.up
  down := storms.down
}

def Storms.insertRight (storms: Storms n m) (row: PFin n) (col: PFin m): Storms n m := {
  left := storms.left
  right := storms.right.push ⟨row, col⟩
  up := storms.up
  down := storms.down
}

def Storms.insertUp (storms: Storms n m) (row: PFin n) (col: PFin m): Storms n m := {
  left := storms.left
  right := storms.right
  up := storms.up.push ⟨row, col⟩
  down := storms.down
}

def Storms.insertDown (storms: Storms n m) (row: PFin n) (col: PFin m): Storms n m := {
  left := storms.left
  right := storms.right
  up := storms.up
  down := storms.down.push ⟨row, col⟩
}

structure Position (n m: Nat) where
  row: Fin n
  col: Fin m
deriving
  Repr, BEq, ReflBEq,
  LawfulBEq, DecidableEq, Hashable

def Position.from (row: PFin (n - 1)) (col: PFin (m - 1)): Position n m :=
  have h1: row.val < n - 1 := row.is_lt
  have h2: col.val < m - 1 := col.is_lt
  let row: Fin n := ⟨row.val, by omega⟩
  let col: Fin m := ⟨col.val, by omega⟩
  ⟨row, col⟩

def Position.updates (p: Position n m): Vector (Position n m) 5 :=
  #v[
    p,
    ⟨p.row.saturatingSucc, p.col⟩,
    ⟨p.row.saturatingPred, p.col⟩,
    ⟨p.row, p.col.saturatingSucc⟩,
    ⟨p.row, p.col.saturatingPred⟩,
  ]

structure Occupied (n m: Nat) where
  storms: Storms (n - 1) (m - 1)
  walls: Std.HashSet (Position n m)

def Occupied.empty: Occupied n m :=
  ⟨⟨#[], #[], #[], #[]⟩, ∅⟩

def Occupied.update (occ: Occupied n m): (Occupied n m) × (Std.HashSet (Position n m)) :=
  let ⟨left, acc⟩ := loop occ.storms.left.toVector occ.walls (fun row col => ⟨row, col.prev⟩)
  let ⟨right, acc⟩ := loop occ.storms.right.toVector acc (fun row col => ⟨row, col.next⟩)
  let ⟨up, acc⟩ := loop occ.storms.up.toVector acc (fun row col => ⟨row.prev, col⟩)
  let ⟨down, acc⟩ := loop occ.storms.down.toVector acc (fun row col => ⟨row.next, col⟩)
  let storms: Storms (n - 1) (m - 1) := {left := left.toArray, right := right.toArray, up := up.toArray, down := down.toArray}
  (⟨storms, occ.walls⟩, acc)
  where loop {k: Nat} (storms: Vector (Blizzard (n - 1) (m - 1)) k) (hazards: Std.HashSet (Position n m)) (f: (PFin (n - 1)) → (PFin (m - 1)) → (PFin (n - 1)) × (PFin (m - 1))): (Vector (Blizzard (n - 1) (m - 1)) k) × (Std.HashSet (Position n m)) :=
    (Fin.foldl k (
      fun ⟨blizzards, hazards⟩ i =>
        let b := blizzards[i]
        let ⟨row, col⟩ := f b.row b.col
        (blizzards.set i ⟨row, col⟩, hazards.insert (Position.from row col))
    ) (storms, hazards))

partial def findGoal (goal: Position n m) (locations: Std.HashSet (Position n m)) (occ: Occupied n m) (time: Nat): Nat × (Occupied n m) :=
  if locations.contains goal then (time, occ)
  else
    let ⟨occ, hazards⟩ := occ.update
    let newLocations := locations.fold (
      fun acc p =>
        p.updates.foldl (
          fun acc q =>
            if hazards.contains q then acc
            else acc.insert q
        ) acc
    ) ∅
    findGoal goal newLocations occ (time + 1)

inductive Tile where
  | wall: Tile
  | empty: Tile
  | left: Tile
  | right: Tile
  | up: Tile
  | down: Tile
deriving
  Repr, BEq, ReflBEq,
  LawfulBEq, DecidableEq, Hashable

def parseTile (x: UInt8): Result Tile :=
  match x with
  | 35 => Except.ok Tile.wall
  | 46 => Except.ok Tile.empty
  | 60 => Except.ok Tile.left
  | 62 => Except.ok Tile.right
  | 94 => Except.ok Tile.up
  | 118 => Except.ok Tile.down
  | _ => Except.error "Unknown tile"

def buildOcc (grid: Grid2D Tile n m): Result (Occupied n m) :=
  Fin.foldlM n (
    fun acc i => Fin.foldlM m (
      fun acc j =>
        let pi := PFin.tryFrom i
        let pj := PFin.tryFrom j
        match grid.get i j with
        | Tile.wall => Except.ok ⟨acc.storms, acc.walls.insert ⟨i, j⟩⟩
        | Tile.empty => Except.ok acc
        | Tile.left => insertStorm acc Storms.insertLeft pi pj
        | Tile.right => insertStorm acc Storms.insertRight pi pj
        | Tile.up => insertStorm acc Storms.insertUp pi pj
        | Tile.down => insertStorm acc Storms.insertDown pi pj
    ) acc
  ) Occupied.empty
  where insertStorm (acc: Occupied n m) (f: (Storms (n - 1) (m - 1)) → (PFin (n - 1)) → (PFin (m - 1)) → (Storms (n - 1) (m - 1))) (pi: Result (PFin (n - 1))) (pj: Result (PFin (m - 1))): Result (Occupied n m) :=
    do
      let row ← pi
      let col ← pj
      pure ⟨f acc.storms row col, acc.walls⟩

def findStart (grid: Grid2D Tile n m): Result (Position n m) := do
  let index ← getOrErr (grid.inner.finIdxOf? Tile.empty) "Failed to find start"
  let ⟨row, col⟩ := lin_index_to_row_col index
  if row.val ≠ 0 then Except.error "Start should be in the first row"
  else pure ⟨row, col⟩

def findEnd (grid: Grid2D Tile n m): Result (Position n m) :=
  Fin.foldl (n * m) (
    fun acc index =>
      let ⟨row, col⟩ := lin_index_to_row_col index
      if row.val ≠ n - 1 then acc
      else match grid.get row col with
      | Tile.empty => Except.ok ⟨row, col⟩
      | _ => acc
  ) (Except.error "Failed to find end")

structure Parsed (n m: Nat) where
  occ: Occupied n m
  start: Position n m
  finish: Position n m

def parseInput (input: String): Result ((n: Nat) × (m: Nat) × (Parsed n m)) := do
  let ⟨n, m, grid⟩ ← parseGrid parseTile input
  let occ ← buildOcc grid
  let start ← findStart grid
  let finish ← findEnd grid
  pure ⟨n, m, ⟨occ, start, finish⟩⟩

def part1Solution (input: String): Result Nat := (parseInput input).map (
  fun ⟨_, _, ⟨occ, start, finish⟩⟩ =>
    let ⟨time, _⟩ := findGoal finish (Std.HashSet.ofList [start]) occ 0
    time
)

def part2Solution (input: String): Result Nat := (parseInput input).map (
  fun ⟨_, _, ⟨occ, start, finish⟩⟩ =>
    let ⟨time, occ⟩ := findGoal finish (Std.HashSet.ofList [start]) occ 0
    let ⟨time, occ⟩ := findGoal start (Std.HashSet.ofList [finish]) occ time
    let ⟨time, _⟩ := findGoal finish (Std.HashSet.ofList [start]) occ time
    time
)
