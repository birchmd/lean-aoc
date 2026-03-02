import AdventOfCode.Common.Fin
import AdventOfCode.Common.Result
import Std.Data.HashSet

inductive WindDirection where
  | right: WindDirection
  | left: WindDirection

def parseWind (line: String.Slice): Result (Array WindDirection) :=
  let mapped := line.bytes.mapM (
    fun b =>
      if b = 62 then Except.ok WindDirection.right
      else if b = 60 then Except.ok WindDirection.left
      else Except.error "Unknown wind symbol"
  )
  mapped.toArray

inductive Shape where
  | dash: Shape
  | plus: Shape
  | corner: Shape
  | pipe: Shape
  | box: Shape
deriving Nonempty, BEq

instance: ToString Shape where
  toString s := match s with
  | Shape.dash => "dash"
  | Shape.plus => "plus"
  | Shape.corner => "corner"
  | Shape.pipe => "pipe"
  | Shape.box => "box"

def Shape.next (s: Shape): Shape := match s with
  | Shape.dash => Shape.plus
  | Shape.plus => Shape.corner
  | Shape.corner => Shape.pipe
  | Shape.pipe => Shape.box
  | Shape.box => Shape.dash

structure Point where
  x: Fin 7
  y: Nat
deriving BEq, Hashable

instance : ToString Point where
  toString p := s!"({p.x} {p.y})"

structure NonEmptyArray α where
  toArray: Array α
  is_non_empty: 0 < toArray.size

def NonEmptyArray.modifyEach (arr: NonEmptyArray α) (f: α → α): NonEmptyArray α :=
  let n := arr.toArray.size
  -- Convert to a vector to make it obvious to Lean that
  -- the size remains unchanged during the fold.
  let xs: Vector α n := arr.toArray.toVector
  let ys := Fin.foldl n (
    fun xs i =>
      let x := xs.get i
      let y := f x
      xs.set i y
  ) xs
  have h1: 0 < n := arr.is_non_empty
  have h2: ys.toArray.size = n := Vector.size_toArray ys
  ⟨ys.toArray, by omega⟩

inductive ShapeState where
  | falling (ps: NonEmptyArray Point): ShapeState
  | atRest (ps: NonEmptyArray Point): ShapeState

def Shape.spawn (s: Shape) (bottom: Nat): NonEmptyArray Point := match s with
  | Shape.dash => ⟨#[⟨2, bottom⟩, ⟨3, bottom⟩, ⟨4, bottom⟩, ⟨5, bottom⟩], by grind⟩
  | Shape.plus => ⟨#[⟨2, bottom + 1⟩, ⟨3, bottom⟩, ⟨3, bottom + 1⟩, ⟨3, bottom + 2⟩, ⟨4, bottom + 1⟩], by grind⟩
  | Shape.corner => ⟨#[⟨2, bottom⟩, ⟨3, bottom⟩, ⟨4, bottom⟩, ⟨4, bottom + 1⟩, ⟨4, bottom + 2⟩], by grind⟩
  | Shape.pipe => ⟨#[⟨2, bottom⟩, ⟨2, bottom + 1⟩, ⟨2, bottom + 2⟩, ⟨2, bottom + 3⟩], by grind⟩
  | Shape.box => ⟨#[⟨2, bottom⟩, ⟨2, bottom + 1⟩, ⟨3, bottom⟩, ⟨3, bottom + 1⟩], by grind⟩

def Shape.pushLeft (ps: NonEmptyArray Point) (blocked: Std.HashSet Point): NonEmptyArray Point :=
  let isBlocked := ps.toArray.any (fun p => (p.x = 0) ∨ blocked.contains ⟨p.x - 1, p.y⟩)
  if isBlocked then ps
  else ps.modifyEach (fun p => ⟨p.x - 1, p.y⟩)

def Shape.pushRight (ps: NonEmptyArray Point) (blocked: Std.HashSet Point): NonEmptyArray Point :=
  let isBlocked := ps.toArray.any (fun p => (p.x = 6) ∨ blocked.contains ⟨p.x + 1, p.y⟩)
  if isBlocked then ps
  else ps.modifyEach (fun p => ⟨p.x + 1, p.y⟩)

def Shape.fall (ps: NonEmptyArray Point) (blocked: Std.HashSet Point): ShapeState :=
  let isBlocked := ps.toArray.any (fun p => (p.y = 0) ∨ blocked.contains ⟨p.x, p.y - 1⟩)
  if isBlocked then ShapeState.atRest ps
  else ShapeState.falling (ps.modifyEach (fun p => ⟨p.x, p.y - 1⟩))

partial def simulation (wind: Vector WindDirection n) (windIndex: Fin n) (s: Shape) (ps: NonEmptyArray Point) (blocked: Std.HashSet Point) (remainingRocks: Nat) (acc: Nat): Nat :=
  if remainingRocks = 0 then acc
  else
  let ps := match wind.get windIndex with
    | WindDirection.right => Shape.pushRight ps blocked
    | WindDirection.left => Shape.pushLeft ps blocked
  match Shape.fall ps blocked with
  | ShapeState.falling ps => simulation wind windIndex.wrappingSucc s ps blocked remainingRocks acc
  | ShapeState.atRest ps =>
    let acc := max acc (ps.toArray.foldl (fun y p => max y (p.y + 1)) 0)
    let blocked := ps.toArray.foldl (fun bs p => bs.insert p) blocked
    let s := s.next
    let ps := Shape.spawn s (acc + 3)
    simulation wind windIndex.wrappingSucc s ps blocked (remainingRocks - 1) acc

structure CROut (n: {n : Nat // n > 0}) where
  nRocks: Nat
  maxHeight: Nat
  nextWindIndex: Fin n
  nextShape: Shape

instance: Nonempty (CROut n) := Nonempty.intro ⟨0, 0, ⟨0, by omega⟩, Shape.dash⟩

def CROut.isSame (a b: CROut n): Bool :=
  a.nextWindIndex == b.nextWindIndex ∧ a.nextShape == b.nextShape

partial def completeRow (n: {n : Nat // n > 0}) (wind: Vector WindDirection n) (windIndex: Fin n) (s: Shape) (ps: NonEmptyArray Point) (blocked: Std.HashSet Point) (acc count: Nat): CROut n :=
    let ps := match wind.get windIndex with
    | WindDirection.right => Shape.pushRight ps blocked
    | WindDirection.left => Shape.pushLeft ps blocked
  match Shape.fall ps blocked with
  | ShapeState.falling ps => completeRow n wind windIndex.wrappingSucc s ps blocked acc count
  | ShapeState.atRest ps =>
    let acc := max acc (ps.toArray.foldl (fun y p => max y (p.y + 1)) 0)
    let blocked := ps.toArray.foldl (fun bs p => bs.insert p) blocked
    let maybeCompleteRow := ps.toArray.find? (
      fun p => Fin.foldl 7 (
        fun q x => q ∧ (blocked.contains ⟨x, p.y⟩)
      ) true
    )
    match maybeCompleteRow with
    | some ⟨_, y⟩ =>
      -- A completed row effectively acts like a new floor.
      -- If there are no extra blocks above the new floor then
      -- we are effectively back to the starting state, except
      -- possibly for the wind position and current shape.
      if blocked.all (fun p => p.y ≤ y) then
        ⟨count + 1, acc, windIndex.wrappingSucc, s.next⟩
      else
        let s := s.next
        let ps := Shape.spawn s (acc + 3)
        completeRow n wind windIndex.wrappingSucc s ps blocked acc (count + 1)
    | none =>
      let s := s.next
      let ps := Shape.spawn s (acc + 3)
      completeRow n wind windIndex.wrappingSucc s ps blocked acc (count + 1)

-- Run the simulation until the whole system cycles back to the same state
partial def completeLoop (n: {n : Nat // n > 0}) (wind: Vector WindDirection n) (state: CROut n): CROut n:=
  let s := state.nextShape
  let ps := Shape.spawn s 3
  let nextState := completeRow n wind state.nextWindIndex s ps (Std.HashSet.ofList []) 0 0
  let totalState: CROut n :=
    ⟨state.nRocks + nextState.nRocks, state.maxHeight + nextState.maxHeight, nextState.nextWindIndex, nextState.nextShape⟩
  if totalState.isSame state then totalState
  else completeLoop n wind totalState

def part1Solution(input: String): Result Nat := (parseWind input.trimAscii).map (
  fun wind =>
    let n := wind.size
    let wind: Vector WindDirection n := wind.toVector
    if h: n = 0 then 0
    else
      let s := Shape.dash
      let ps := Shape.spawn s 3
      simulation wind ⟨0, by omega⟩ s ps (Std.HashSet.ofList []) 2022 0
)

def part2Solution(input: String): Result Nat := (parseWind input.trimAscii).map (
  fun wind =>
    let n := wind.size
    let wind: Vector WindDirection n := wind.toVector
    if h: n = 0 then 0
    else
      let n: {n : Nat // n > 0} := ⟨n, by omega⟩
      let s := Shape.dash
      let ps := Shape.spawn s 3
      let out := completeRow n wind ⟨0, by omega⟩ s ps (Std.HashSet.ofList []) 0 0
      let loopState := completeLoop n wind out
      let ps := Shape.spawn loopState.nextShape 3
      let deltaState := completeRow n wind loopState.nextWindIndex loopState.nextShape ps (Std.HashSet.ofList []) 0 0
      -- We know `deltaState` is a fixed point of the `completeRow` function by
      -- construction. Now we need to try to get to 1 trillion rocks.
      let repeats := (1000000000000 - loopState.nRocks) / deltaState.nRocks
      let remainingRuns := (1000000000000 - loopState.nRocks) % deltaState.nRocks
      let repeatHeight := deltaState.maxHeight * repeats
      let extraHeight := simulation wind loopState.nextWindIndex loopState.nextShape ps (Std.HashSet.ofList []) remainingRuns 0
      loopState.maxHeight + repeatHeight + extraHeight
)
