import AdventOfCode.Common.Result
import Std.Data.HashSet

structure Point where
  x: Int
  y: Int
deriving BEq, Hashable

instance : ToString Point where
  toString p := s!"({p.x}, {p.y})"

structure State where
  noBeacons: Std.HashSet Int
  beacons: Std.HashSet Int

def State.empty: State :=
  ⟨Std.HashSet.ofList [], Std.HashSet.ofList []⟩

structure State2 where
  sources: Array (Point × Nat)
  visited: Std.HashSet Point
--  cache: Std.HashMap Point Nat

def abs(x: Int): Nat :=
  x.natAbs

def manhattanDistance (p q: Point): Nat :=
  abs (p.x - q.x) + abs (p.y - q.y)

def intersect (p: Point) (r: Nat) (y: Int) (values: Std.HashSet Int): Std.HashSet Int :=
  let d := abs (p.y - y)
  if r < d then values
  else
    let dx := r - d
    Fin.foldl (dx + 1) (
      fun acc i =>
        (acc.insert (p.x + i)).insert (p.x - i)
    ) values

def parseLine (line: String.Slice): Result (Point × Point) :=
  match ((line.split " ").filter (fun x => x.contains "=")).toList with
  | x1 :: y1 :: x2 :: y2 :: [] =>
    let x1 := (x1.dropPrefix "x=").dropSuffix ","
    let y1 := (y1.dropPrefix "y=").dropSuffix ":"
    let x2 := (x2.dropPrefix "x=").dropSuffix ","
    let y2 := (y2.dropPrefix "y=")
    do
      let x1 ← getOrErr x1.toInt? "Failed to parse x1"
      let y1 ← getOrErr y1.toInt? "Failed to parse y1"
      let x2 ← getOrErr x2.toInt? "Failed to parse x2"
      let y2 ← getOrErr y2.toInt? "Failed to parse y2"
      pure (⟨x1, y1⟩, ⟨x2, y2⟩)
  | _ => Except.error "Failed to parse line"

def insertPoints (y: Int) (state: State) (pq: Point × Point): State :=
  let ⟨p, q⟩ := pq
  let r := manhattanDistance p q
  let noBeacons := intersect p r y state.noBeacons
  let beacons := if q.y = y then state.beacons.insert q.x else state.beacons
  ⟨noBeacons, beacons⟩

def sourcesContain (size: Int) (x: Point) (sources: Array (Point × Nat)): Bool :=
  if x.x < 0 ∨ size < x.x then true
  else if x.y < 0 ∨ size < x.y then true
  else sources.any (fun ⟨s, r⟩ => manhattanDistance s x ≤ r)

def searchSingle (size: Int) (sources: Array (Point × Nat)) (s: Point) (r: Nat): Option Point :=
  let x0 := s.x + r + 1
  let y0 := s.y
  loop x0 y0 (r + 1)
  where loop (x: Int) (y: Int) (d: Nat): Option Point :=
    let p: Point := ⟨x, y⟩
    if d = 0 then none
    else if sourcesContain size p sources then loop (x - 1) (y + 1) (d - 1)
    else some p

def search (size: Int) (sources: Array (Point × Nat)): Option Point :=
  let n := sources.size
  if h: n = 0 then none
  else
    loop ⟨0, by omega⟩
  where loop (i: Fin (sources.size)): Option Point :=
    let ⟨s, r⟩ := sources.getInternal i.val i.is_lt
    match searchSingle size sources s r with
    | some p => some p
    | none =>
      if h: (i + 1) < sources.size then
        loop ⟨i + 1, h⟩
      else none

def part1Solution(input: String): Result Nat :=
  let y := 2000000
  let state := ((input.trimAscii.split "\n").mapM parseLine).fold (insertPoints y) State.empty
  state.map (
    fun state => (state.noBeacons.diff state.beacons).size
  )

def part2Solution(input: String): Result Int :=
  let size := 4000000
  let sources := ((input.trimAscii.split "\n").mapM parseLine).toArray
  sources.map (
    fun sources =>
      let sources := sources.map (fun ⟨s, b⟩ => ⟨s, manhattanDistance s b⟩)
      match search size sources with
      | some ⟨x, y⟩ => 4000000 * x + y
      | none => dbgTrace "Failed to find" (fun () => 0)
  )
