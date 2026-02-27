import AdventOfCode.Common.Result
import Std.Data.HashSet

structure Point where
  x: Int
  y: Nat
deriving BEq, Hashable

def Point.down (p: Point): Point := ⟨p.x, p.y + 1⟩
def Point.downLeft (p: Point): Point := ⟨p.x - 1, p.y + 1⟩
def Point.downRight (p: Point): Point := ⟨p.x + 1, p.y + 1⟩

def minMax [LT α] [DecidableLT α] (a b: α): α × α :=
  if a < b then (a, b)
  else (b, a)

def parsePoint (input: String.Slice): Result Point :=
  match (input.split ",").toList with
  | x :: y :: [] => do
    let x ← getOrErr x.toInt? "Failed to parse x"
    let y ← getOrErr y.toNat? "Failed to parse y"
    pure ⟨x, y⟩
  | _ => Except.error "Failed to parse point"

def fillRange (blocked: Std.HashSet Point) (p1 p2: Point): Std.HashSet Point :=
  let ⟨minX, maxX⟩ := minMax p1.x p2.x
  let ⟨minY, maxY⟩ := minMax p1.y p2.y
  (minX...=maxX).iter.fold (
      fun acc x =>
        (minY...=maxY).iter.fold (
          fun acc y =>
            let p: Point := ⟨x, y⟩
            acc.insert p
        ) acc
  ) blocked

def insertRock (blocked: Std.HashSet Point) (line: String.Slice): Result (Std.HashSet Point) :=
  ((line.split " -> ").mapM parsePoint).toList.map (
    fun points => match points with
    | [] => blocked
    | _ :: tail => (points.iter.zip (tail.iter)).fold (
      fun acc ⟨p1, p2⟩ => fillRange acc p1 p2
    ) blocked
  )

def fallingSand (blocked: Std.HashSet Point) (maxHeight: Nat) (sand: Point): Option (Std.HashSet Point) :=
  if maxHeight ≤ sand.y then none
  else if ¬(blocked.contains sand.down) then fallingSand blocked maxHeight sand.down
  else if ¬(blocked.contains sand.downLeft) then fallingSand blocked maxHeight sand.downLeft
  else if ¬(blocked.contains sand.downRight) then fallingSand blocked maxHeight sand.downRight
  else some (blocked.insert sand)
termination_by maxHeight - sand.y
decreasing_by
  . simp [Point.down]; omega
  . simp [Point.downLeft]; omega
  . simp [Point.downRight]; omega

def fallingSandWithFloor (blocked: Std.HashSet Point) (floorHeight: Nat) (sand: Point) (h: sand.y < floorHeight): Std.HashSet Point :=
  if h1: sand.y + 1 = floorHeight then blocked.insert sand
  else
    have h2: sand.y + 1 < floorHeight := by omega
    if ¬(blocked.contains sand.down) then fallingSandWithFloor blocked floorHeight sand.down (by simp [Point.down, h2])
    else if ¬(blocked.contains sand.downLeft) then fallingSandWithFloor blocked floorHeight sand.downLeft (by simp [Point.downLeft, h2])
    else if ¬(blocked.contains sand.downRight) then fallingSandWithFloor blocked floorHeight sand.downRight ((by simp [Point.downRight, h2]))
    else blocked.insert sand
termination_by floorHeight - sand.y
decreasing_by
  . simp [Point.down]; omega
  . simp [Point.downLeft]; omega
  . simp [Point.downRight]; omega

-- This function really is partial because if the walls containing the sand
-- bound the source then it will never overflow.
partial def countFallingSand (blocked: Std.HashSet Point) (maxHeight count: Nat): Nat :=
  match fallingSand blocked maxHeight ⟨500, 0⟩ with
  | none => count
  | some blocked => countFallingSand blocked maxHeight (count + 1)

-- I think this function probably does terminate for all inputs, but formally proving it
-- seems hard. Intuitively it would go something like: if `blocked` is empty then then
-- a pile builds up on the floor until the source is blocked; if `blocked` is non-empty then
-- the width of the pile is constrained and it builds up to the source even faster.
partial def countFallingSandWithFloor (blocked: Std.HashSet Point) (floorHeight count: Nat) (h: 0 < floorHeight): Nat :=
  let source: Point := ⟨500, 0⟩
  let blocked := fallingSandWithFloor blocked floorHeight source (by omega)
  if blocked.contains source then count + 1
  else countFallingSandWithFloor blocked floorHeight (count + 1) h

def parseInput (input: String): Result (Std.HashSet Point) :=
  (input.trimAscii.split "\n").foldM insertRock (Std.HashSet.ofList [])

def part1Solution(input: String): Result Nat := (parseInput input).map (
  fun blocked =>
    let maxHeight := blocked.fold (fun h p => max h p.y) 0
    countFallingSand blocked maxHeight 0
)

def part2Solution(input: String): Result Nat := (parseInput input).map (
  fun blocked =>
    let maxHeight := blocked.fold (fun h p => max h p.y) 0
    let floorHeight := maxHeight + 2
    countFallingSandWithFloor blocked floorHeight 0 (by omega)
)

-- Theorems for the `minMax` function.
theorem min_max_eq [LT α] [DecidableLT α] (a: α): minMax a a = (a, a) := by simp [minMax]
theorem min_max_lt [LT α] [DecidableLT α] (a b: α) (h: a < b): minMax a b = (a, b) := by simp [minMax, h]
theorem min_max_ge [LT α] [DecidableLT α] (a b: α) (h: ¬(a < b)): minMax a b = (b, a) := by simp [minMax, h]
