import AdventOfCode.Common.Result
import Std.Data.HashSet
import Init.Util

structure Point where
  x: Int
  y: Int
deriving Hashable, BEq

def Point.Zero: Point := ⟨ 0, 0 ⟩

instance: ToString Point where
  toString pt := s!"({pt.x}, {pt.y})"

inductive LR where
| Left: LR
| Right: LR

inductive UD where
| Up: UD
| Down: UD

inductive OrthogonalDirection where
| x (d: LR): OrthogonalDirection
| y (d: UD): OrthogonalDirection

def OrthogonalDirection.opposite (d: OrthogonalDirection): OrthogonalDirection :=
  match d with
  | OrthogonalDirection.x LR.Left => OrthogonalDirection.x LR.Right
  | OrthogonalDirection.x LR.Right => OrthogonalDirection.x LR.Left
  | OrthogonalDirection.y UD.Up => OrthogonalDirection.y UD.Down
  | OrthogonalDirection.y UD.Down => OrthogonalDirection.y UD.Up

inductive TailDirection where
| ortho (d: OrthogonalDirection): TailDirection
| Center: TailDirection
| diag (x: LR) (y: UD): TailDirection

structure State where
  head: Point
  tail: TailDirection
  visited: Std.HashSet Point

def State.start: State :=
  ⟨ Point.Zero, TailDirection.Center, Std.HashSet.ofList [Point.Zero] ⟩

structure State2 where
  head: Point
  tails: Vector TailDirection 9
  visited: Std.HashSet Point

def State2.start: State2 :=
  ⟨ Point.Zero, Vector.replicate 9 TailDirection.Center, Std.HashSet.ofList [Point.Zero] ⟩

def endPoint (pt: Point) (dir: OrthogonalDirection): Point := match dir with
  | OrthogonalDirection.x LR.Left => ⟨ pt.x - 1, pt.y ⟩
  | OrthogonalDirection.x LR.Right => ⟨ pt.x + 1, pt.y ⟩
  | OrthogonalDirection.y UD.Up => ⟨ pt.x, pt.y + 1 ⟩
  | OrthogonalDirection.y UD.Down => ⟨ pt.x, pt.y - 1 ⟩

def tailPoint (head: Point) (tail: TailDirection): Point := match tail with
  | TailDirection.ortho d => endPoint head d
  | TailDirection.Center => ⟨ head.x, head.y ⟩
  | TailDirection.diag LR.Left UD.Up => ⟨ head.x - 1, head.y + 1 ⟩
  | TailDirection.diag LR.Left UD.Down => ⟨ head.x - 1, head.y - 1 ⟩
  | TailDirection.diag LR.Right UD.Up => ⟨ head.x + 1, head.y + 1 ⟩
  | TailDirection.diag LR.Right UD.Down => ⟨ head.x + 1, head.y - 1 ⟩

def newTailDirection (hp tp: Point): TailDirection :=
  let dx := tp.x - hp.x
  let dy := tp.y - hp.y
  match (dx, dy) with
    | (0, 0) => TailDirection.Center
    | (1, 0) => TailDirection.ortho (OrthogonalDirection.x LR.Right)
    | (-1, 0) => TailDirection.ortho (OrthogonalDirection.x LR.Left)
    | (0, 1) => TailDirection.ortho (OrthogonalDirection.y UD.Up)
    | (0, -1) => TailDirection.ortho (OrthogonalDirection.y UD.Down)
    | (1, 1) => TailDirection.diag LR.Right UD.Up
    | (1, -1) => TailDirection.diag LR.Right UD.Down
    | (-1, 1) => TailDirection.diag LR.Left UD.Up
    | (-1, -1) => TailDirection.diag LR.Left UD.Down
    | (2, 0) => TailDirection.ortho (OrthogonalDirection.x LR.Right)
    | (-2, 0) => TailDirection.ortho (OrthogonalDirection.x LR.Left)
    | (0, 2) => TailDirection.ortho (OrthogonalDirection.y UD.Up)
    | (0, -2) => TailDirection.ortho (OrthogonalDirection.y UD.Down)
    | (2, 1) => TailDirection.ortho (OrthogonalDirection.x LR.Right)
    | (2, -1) => TailDirection.ortho (OrthogonalDirection.x LR.Right)
    | (-2, 1) => TailDirection.ortho (OrthogonalDirection.x LR.Left)
    | (-2, -1) => TailDirection.ortho (OrthogonalDirection.x LR.Left)
    | (1, 2) => TailDirection.ortho (OrthogonalDirection.y UD.Up)
    | (-1, 2) => TailDirection.ortho (OrthogonalDirection.y UD.Up)
    | (1, -2) => TailDirection.ortho (OrthogonalDirection.y UD.Down)
    | (-1, -2) => TailDirection.ortho (OrthogonalDirection.y UD.Down)
    | (2, 2) => TailDirection.diag LR.Right UD.Up
    | (2, -2) => TailDirection.diag LR.Right UD.Down
    | (-2, 2) => TailDirection.diag LR.Left UD.Up
    | (-2, -2) => TailDirection.diag LR.Left UD.Down
    -- TODO: should limit the input types so the above list is exhaustive.
    -- In how this function is used this final case is unreachable.
    | _ => TailDirection.Center

def move (state: State) (direction: OrthogonalDirection): State :=
  let tp := tailPoint state.head state.tail
  let hp := endPoint state.head direction
  let td := newTailDirection hp tp
  let tp := tailPoint hp td
  let visited := state.visited.insert tp
  ⟨ hp, td, visited ⟩

def move2 (state: State2) (direction: OrthogonalDirection): State2 :=
  let hp := endPoint state.head direction
  let ⟨_, tp, tails⟩ := Fin.foldl 9 (
    fun ⟨hp, hp2, tails⟩ i =>
      let tp := tailPoint hp (tails.get i)
      let td := newTailDirection hp2 tp
      let tp2 := tailPoint hp2 td
      (tp, tp2, tails.set i td)
  ) (state.head, hp, state.tails)
  let visited := state.visited.insert tp
  ⟨ hp, tails, visited ⟩

def doMove (moveFn: α → OrthogonalDirection → α) (state: α) (line: String.Slice): Result α :=
  match (line.split " ").toList with
  | d :: n :: [] =>
    let n: Result Nat := getOrErr n.toNat? "Failed to parse number"
    let dir: Result OrthogonalDirection := match d.toString with
      | "R" => Except.ok (OrthogonalDirection.x LR.Right)
      | "L" => Except.ok (OrthogonalDirection.x LR.Left)
      | "U" => Except.ok (OrthogonalDirection.y UD.Up)
      | "D" => Except.ok (OrthogonalDirection.y UD.Down)
      | _ => Except.error "Failed to parse direction"
    do
      let n ← n
      let dir ← dir
      pure (Fin.foldl n (fun s _ => moveFn s dir) state)
  | _ => Except.error "Failed to parse line"

def part1Solution(input: String): Result Nat := do
  let state ← (input.trimAscii.split "\n").foldM (doMove move) State.start
  let n := state.visited.size
  pure n

def part2Solution(input: String): Result Nat := do
  let state ← (input.trimAscii.split "\n").foldM (doMove move2) State2.start
  let n := state.visited.size
  pure n

-- Theorems proving the correctness of the tail movement
theorem tail_direction_id (hp: Point) (td: TailDirection): newTailDirection hp (tailPoint hp td) = td :=
  match td with
  | TailDirection.ortho (OrthogonalDirection.x lr) => by cases lr <;> simp+arith [tailPoint, endPoint, newTailDirection]
  | TailDirection.ortho (OrthogonalDirection.y ud) => by cases ud <;> simp+arith [tailPoint, endPoint, newTailDirection]
  | TailDirection.Center => by simp [tailPoint, newTailDirection]
  | TailDirection.diag x y => by cases x <;> cases y <;> simp+arith [tailPoint, newTailDirection]

theorem step_from_center (hp: Point) (dir: OrthogonalDirection): newTailDirection (endPoint hp dir) (tailPoint hp TailDirection.Center) = TailDirection.ortho dir.opposite :=
  match dir with
  | OrthogonalDirection.x lr => by cases lr <;> simp+arith [endPoint, tailPoint, newTailDirection, OrthogonalDirection.opposite]
  | OrthogonalDirection.y ud => by cases ud <;> simp+arith [endPoint, tailPoint, newTailDirection, OrthogonalDirection.opposite]
