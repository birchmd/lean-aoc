import AdventOfCode.Common.Result
import Std.Data.HashSet

structure Point where
  x: Int
  y: Int
  z: Int
deriving BEq, Hashable

instance: EquivBEq Point where
  rfl := by simp [BEq.beq, instBEqPoint.beq]
  symm := by simp [BEq.beq, instBEqPoint.beq]; grind
  trans := by simp [BEq.beq, instBEqPoint.beq]; grind

instance: LawfulHashable Point where
  hash_eq := by
    simp [Hashable.hash, instHashablePoint.hash, BEq.beq, instBEqPoint.beq]
    grind

instance: ToString Point where
  toString p :=
    let ⟨x, y, z⟩ := p
    s!"({x}, {y}, {z})"

def Point.neighbours (p: Point): Vector Point 6 := #v[
  ⟨p.x + 1, p.y, p.z⟩,
  ⟨p.x - 1, p.y, p.z⟩,
  ⟨p.x, p.y + 1, p.z⟩,
  ⟨p.x, p.y - 1, p.z⟩,
  ⟨p.x, p.y, p.z + 1⟩,
  ⟨p.x, p.y, p.z - 1⟩,
]

def Point.zipMap (p q: Point) (f: Int → Int → Int): Point :=
  ⟨f p.x q.x, f p.y q.y, f p.z q.z⟩

def foldRange (min max: Int) (f: α → Int → α) (init: α): α :=
  if min ≤ max then loop min (max - min).natAbs.succ init
  else init
  where loop (i: Int) (j: Nat) (x: α): α :=
    if j = 0 then x
    else loop (i + 1) (j - 1) (f x i)

def Point.boundingBox (p q: Point) (f: α → Point → α) (init: α): α :=
  foldRange p.x q.x (
    fun a x =>
      foldRange p.y q.y (
        fun a y => foldRange p.z q.z (
          fun a z => f a ⟨x, y, z⟩
        ) a
      ) a
  ) init

def parsePoint (line: String.Slice): Result Point :=
  match (line.split ",").toList with
  | x :: y :: z :: [] => do
    let x ← getOrErr x.toInt? "Failed to parse x"
    let y ← getOrErr y.toInt? "Failed to parse y"
    let z ← getOrErr z.toInt? "Failed to parse z"
    pure ⟨x, y, z⟩
  | _ => Except.error "Failed to parse point"

structure LavaDrop where
  points: Std.HashSet Point
  surfaceArea: Nat
  minPt: Point
  maxPt: Point

def LavaDrop.empty: LavaDrop := ⟨∅, 0, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩

def LavaDrop.insert (drop: LavaDrop) (p: Point): LavaDrop :=
  let adj := p.neighbours.foldl (fun acc q => if drop.points.contains q then acc + 1 else acc) 0
  let minPt := if drop.points.isEmpty then p else drop.minPt.zipMap p min
  let maxPt := if drop.points.isEmpty then p else drop.maxPt.zipMap p max
  ⟨
    drop.points.insert p,
    drop.surfaceArea + 6 - 2 * adj,
    minPt,
    maxPt
  ⟩

-- Lemmas that help prove the termination of `LavaDrop.fillExterior`
theorem hashset_size_erase (set: Std.HashSet Point) (p: Point) (h: set.contains p = true): (set.erase p).size = set.size - 1 := by
  have h1: p ∈ set := by grind
  rw [Std.HashSet.size_erase]
  simp [h1]

theorem hashset_size_non_empty (set: Std.HashSet Point) (p: Point) (h: set.contains p = true): 1 ≤ set.size := by
  have h1: set.isEmpty = false := by
    rw [Std.HashSet.isEmpty_eq_false_iff_exists_contains_eq_true]
    grind
  have h2: set.size ≠ 0 := by rw [Std.HashSet.isEmpty_eq_size_eq_zero] at h1; grind
  omega

def LavaDrop.fillExterior (drop: LavaDrop) (stack: List Point) (emptyPoints: Std.HashSet Point): Std.HashSet Point :=
  match stack with
  | [] => emptyPoints
  | p :: tail =>
    if emptyPoints.contains p then
      let emptyPointsMinusP := emptyPoints.erase p
      let stack := p.neighbours.foldl (fun s q => q :: s) tail
      drop.fillExterior stack emptyPointsMinusP
    else drop.fillExterior tail emptyPoints
termination_by stack.length + 7 * emptyPoints.size
decreasing_by
  . simp [Vector.foldl]
    have h1: emptyPoints.contains p = true := by trivial
    have h2: emptyPointsMinusP.size = emptyPoints.size - 1 := hashset_size_erase emptyPoints p h1
    have h3: 7 * (emptyPoints.size - 1) = 7 * emptyPoints.size - 7 := by grind
    have h4: 1 ≤ emptyPoints.size := hashset_size_non_empty emptyPoints p h1
    rw [h2, h3]
    omega
  . grind

-- Idea: to get the interior surface area we first find all empty spaces
-- that are with a region bounding the `LavaDrop` (bounding box), then
-- exclude all the empty spaces that are outside the drop using a sort of
-- space fill algorithm. The remaining empty spaces must be interior to the
-- `LavaDrop`, so to finish it off we just need to count all the faces that are
-- adjacent to these interior empty spaces.
def LavaDrop.interiorSurfaceArea (drop: LavaDrop): Nat :=
  let outside: Point := ⟨drop.minPt.x - 1, drop.minPt.y - 1, drop.minPt.z - 1⟩
  let emptyPoints := outside.boundingBox drop.maxPt (
    fun set p => if drop.points.contains p then set else set.insert p
  ) ∅
  let interiorEmptyPoints := drop.fillExterior [outside] emptyPoints
  interiorEmptyPoints.fold (
    fun acc p =>
      p.neighbours.foldl (fun sa q => if drop.points.contains q then sa + 1 else sa) acc
  ) 0

def part1Solution(input: String): Result Nat :=
  let drop := ((input.trimAscii.split "\n").mapM parsePoint).fold LavaDrop.insert LavaDrop.empty
  drop.map (fun d => d.surfaceArea)

def part2Solution(input: String): Result Nat :=
  let drop := ((input.trimAscii.split "\n").mapM parsePoint).fold LavaDrop.insert LavaDrop.empty
  drop.map (fun d => d.surfaceArea - d.interiorSurfaceArea)
