import AdventOfCode.Common.Grid2D
import AdventOfCode.Common.Result
import Std.Data.HashSet
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

deriving instance Hashable for Zsqrtd
deriving instance Hashable for GaussianInt

structure Direction where
  inner: GaussianInt
deriving
  Repr, BEq, ReflBEq,
  LawfulBEq, DecidableEq,
  Nonempty, Hashable

structure Position where
  inner: GaussianInt
deriving
  Repr, BEq, ReflBEq,
  LawfulBEq, DecidableEq,
  Nonempty, Hashable

instance: ToString Position where
  toString p := s!"({p.inner.re}, {p.inner.im})"

def Position.minXY (p q : Position): Position :=
  let x := min (p.inner.re) (q.inner.re)
  let y := min (p.inner.im) (q.inner.im)
  ⟨⟨x, y⟩⟩

def Position.maxXY (p q : Position): Position :=
  let x := max (p.inner.re) (q.inner.re)
  let y := max (p.inner.im) (q.inner.im)
  ⟨⟨x, y⟩⟩

-- Keys of this map are post-move
-- occupied positions (i.e. destinations),
-- values are the positions the elves came from
-- (i.e. sources). Since multiple elves
-- are not allowed to move into the same space
-- we will filter the map to only contain
-- values with a single element in its list.
structure Occupied where
  inner: Std.HashSet Position

structure State where
  occupied: Occupied
  priority: Vector Direction 4

-- Move to a new position in a certain direction
instance: HAdd Position Direction Position where
  hAdd p d := ⟨p.inner + d.inner⟩

def N: Direction := ⟨⟨-1, 0⟩⟩
def E: Direction := ⟨⟨0, 1⟩⟩
def S: Direction := ⟨-N.inner⟩
def W: Direction := ⟨-E.inner⟩

def NE: Direction := ⟨N.inner + E.inner⟩
def NW: Direction := ⟨N.inner + W.inner⟩
def SE: Direction := ⟨S.inner + E.inner⟩
def SW: Direction := ⟨S.inner + W.inner⟩

-- Returns a vector with a central direction
-- and its two nearest diagonals.
-- e.g. `N => #v[NW, N, NE]`
def diag (d: Direction): Vector Direction 3 :=
  let dPerp := d.inner * E.inner
  #v[⟨d.inner - dPerp⟩, d, ⟨d.inner + dPerp⟩]

-- Encodes the propose move rule from the puzzle
-- e.g. "If there is no Elf in the N, NE, or
-- NW adjacent positions, the Elf proposes moving north one step."
def proposeMoveInDirection
  (x: Position)
  (occupied: Occupied)
  (d: Direction): Option Position
:=
  let ys := (diag d).toArray.iter.map (HAdd.hAdd x)
  if ys.any (fun y => occupied.inner.contains y) then none
  else some (x + d)

-- Recursive helper function
def proposeMoveAux
  (x: Position)
  (occupied: Occupied)
  (priority: Vector Direction 4)
  (i: Fin 4): Option Position
:=
  match proposeMoveInDirection x occupied (priority.get i) with
  | some p => some p
  | none =>
    if h: i.val + 1 < 4 then
      proposeMoveAux x occupied priority ⟨i.val + 1, by omega⟩
    else none

def proposeMove
  (x: Position)
  (occupied: Occupied)
  (priority: Vector Direction 4): Option Position
:=
  if #[N, NE, E, SE, S, SW, W, NW].any (fun d => occupied.inner.contains (x + d)) then
    proposeMoveAux x occupied priority ⟨0, by omega⟩
  else none

def rotatePriority (priority: Vector Direction 4): Vector Direction 4 :=
  let a := priority[0]
  let b := priority[1]
  let c := priority[2]
  let d := priority[3]
  #v[b, c, d, a]

def doRound (state: State): State × Bool :=
  let proposedMoves: Std.HashMap Position (List Position) :=
    state.occupied.inner.fold (
      fun acc x =>
        match proposeMove x state.occupied state.priority with
        | none => acc
        | some p => match acc.get? p with
          | some list => acc.insert p (x :: list)
          | none => acc.insert p [x]
    ) ∅
  let ⟨newOccupied, moved⟩ := proposedMoves.fold (
    fun ⟨acc, moved⟩ dst srcList => match srcList with
      | [x] => ((acc.erase x).insert dst, true)
      | _ => (acc, moved)
  ) (state.occupied.inner, false)
  (⟨⟨newOccupied⟩, rotatePriority state.priority⟩, moved)

def doRound1 (state: State): State :=
  let proposedMoves: Std.HashMap Position (List Position) :=
    state.occupied.inner.fold (
      fun acc x =>
        match proposeMove x state.occupied state.priority with
        | none => acc
        | some p => match acc.get? p with
          | some list => acc.insert p (x :: list)
          | none => acc.insert p [x]
    ) ∅
  let newOccupied := proposedMoves.fold (
    fun acc dst srcList => match srcList with
      | [x] => (acc.erase x).insert dst
      | _ => acc
  ) state.occupied.inner
  ⟨⟨newOccupied⟩, rotatePriority state.priority⟩

partial def countRounds (state: State) (acc: Nat): Nat :=
  let ⟨newState, moved⟩ := doRound state
  if moved then countRounds newState (acc + 1)
  else acc + 1

def parseInput (input: String): Result State := do
  let ⟨n, m, grid⟩ ← parseGrid (
    fun b => Except.ok (b == 35)
  ) input
  let occupied: Std.HashSet Position :=
    Fin.foldl n (
      fun acc i => Fin.foldl m (
        fun acc j =>
          if grid.get i j then acc.insert ⟨⟨i.val, j.val⟩⟩
          else acc
      ) acc
    ) ∅
  let priority := #v[N, S, W, E]
  pure ⟨⟨occupied⟩, priority⟩

def part1Solution (input: String): Result Nat := (parseInput input).map (
  fun state =>
    let state := Fin.foldl 10 (
      fun acc _ => doRound1 acc
    ) state
    let ps := state.occupied.inner.inner.keysArray
    if h: ps.size = 0 then 0
    else
      let ⟨lb, ub⟩ := ps.foldl (
        fun ⟨lb, ub⟩ p => (lb.minXY p, ub.maxXY p)
      ) (ps[0], ps[0])
      let n := (ub.inner.re - lb.inner.re + 1).natAbs
      let m := (ub.inner.im - lb.inner.im + 1).natAbs
      Fin.foldl n (
        fun acc i => Fin.foldl m (
          fun acc j =>
            let p: Position := ⟨⟨lb.inner.re + i, lb.inner.im + j⟩⟩
            if state.occupied.inner.contains p then acc
            else acc + 1
        ) acc
      ) 0
)

def part2Solution (input: String): Result Nat := (parseInput input).map (
 fun state => countRounds state 0
)

-- The priority list cycles after 4 times
theorem rotate_priority_4 (p: Vector Direction 4): (rotatePriority (rotatePriority (rotatePriority (rotatePriority p)))) = p :=
  by repeat simp [rotatePriority]; grind

theorem diag_n_works: diag N = #v[NE, N, NW] := by
  simp [diag, N, NW, NE, W, E]
  trivial

theorem diag_s_works: diag S = #v[SW, S, SE] := by
  simp [diag]
  trivial

theorem diag_e_works: diag E = #v[SE, E, NE] := by
  simp [diag]
  trivial

theorem diag_w_works: diag W = #v[NW, W, SW] := by
  simp [diag]
  trivial
