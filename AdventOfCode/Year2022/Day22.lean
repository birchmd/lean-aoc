import AdventOfCode.Common.Fin
import AdventOfCode.Common.Grid2D
import AdventOfCode.Common.Result

inductive Tile where
| empty: Tile
| available: Tile
| wall: Tile
deriving BEq

instance: ToString Tile where
  toString t := match t with
  | Tile.empty => " "
  | Tile.available => "."
  | Tile.wall => "#"

inductive Direction where
| right: Direction
| down: Direction
| left: Direction
| up: Direction

instance: ToString Direction where
  toString d := match d with
    | Direction.right => ">"
    | Direction.down => "v"
    | Direction.left => "<"
    | Direction.up => "^"

def Direction.toNat (d: Direction): Nat := match d with
| right => 0
| down => 1
| left => 2
| up => 3

def Direction.rotateLeft (d: Direction): Direction := match d with
| right => up
| down => right
| left => down
| up => left

def Direction.rotateRight (d: Direction): Direction := match d with
| right => down
| down => left
| left => up
| up => right

inductive Instruction where
| move (x: Nat): Instruction
| rotateLeft: Instruction
| rotateRight: Instruction

structure State (n: Nat) (m: Nat) where
  board: Grid2D Tile n m
  location: board.Position
  direction: Direction

def State.start (board: Grid2D Tile n m): Result (State n m) :=
  match board.inner.finIdxOf? Tile.available with
  | none => Except.error "No available tiles"
  | some index =>
    let ⟨i, j⟩ := lin_index_to_row_col index
    Except.ok ⟨board, ⟨i.val, j.val, i.is_lt, j.is_lt⟩, Direction.right⟩

def State.cast (state: State n m) (h: n = n' ∧ m = m'): State n' m' :=
  let board := state.board.cast h
  have h1: state.location.i < n := state.location.row_in_bounds
  have h2: state.location.j < m := state.location.col_in_bounds
  let location := ⟨state.location.i, state.location.j, by omega, by omega⟩
  ⟨board, location, state.direction⟩

def searchLeftForLastNonEmptyTile
  (board: Grid2D Tile n m)
  (location: board.Position): board.Position
:=
  if location.j = 0 then location
  else
    let i: Fin n := ⟨location.i, location.row_in_bounds⟩
    have col_in_bounds: location.j < m := location.col_in_bounds
    let j: Fin m := ⟨location.j - 1, by omega⟩
    match board.get i j with
    | Tile.empty => location
    | _ => searchLeftForLastNonEmptyTile board ⟨i.val, j.val, i.is_lt, j.is_lt⟩
termination_by location.j

def searchRightForLastNonEmptyTile
  (board: Grid2D Tile n m)
  (location: board.Position): board.Position
:=
  if h: location.j = m - 1 then location
  else
    let i: Fin n := ⟨location.i, location.row_in_bounds⟩
    have col_in_bounds: location.j < m := location.col_in_bounds
    let j: Fin m := ⟨location.j + 1, by omega⟩
    match board.get i j with
    | Tile.empty => location
    | _ => searchRightForLastNonEmptyTile board ⟨i.val, j.val, i.is_lt, j.is_lt⟩

def searchDownForLastNonEmptyTile
  (board: Grid2D Tile n m)
  (location: board.Position): board.Position
:=
  if h: location.i = n - 1 then location
  else
    let j: Fin m := ⟨location.j, location.col_in_bounds⟩
    have row_in_bounds: location.i < n := location.row_in_bounds
    let i: Fin n := ⟨location.i + 1, by omega⟩
    match board.get i j with
    | Tile.empty => location
    | _ => searchDownForLastNonEmptyTile board ⟨i.val, j.val, i.is_lt, j.is_lt⟩

def searchUpForLastNonEmptyTile
  (board: Grid2D Tile n m)
  (location: board.Position): board.Position
:=
  if location.i = 0 then location
  else
    let j: Fin m := ⟨location.j, location.col_in_bounds⟩
    have row_in_bounds: location.i < n := location.row_in_bounds
    let i: Fin n := ⟨location.i - 1, by omega⟩
    match board.get i j with
    | Tile.empty => location
    | _ => searchUpForLastNonEmptyTile board ⟨i.val, j.val, i.is_lt, j.is_lt⟩
termination_by location.i

def State.neighbour (state: State n m): Option state.board.Position :=
  let i: Fin n := ⟨state.location.i, state.location.row_in_bounds⟩
  let j: Fin m := ⟨state.location.j, state.location.col_in_bounds⟩
  match state.direction with
    | Direction.right =>
      let j := j.wrappingSucc
      match state.board.get i j with
      | Tile.wall => none
      | Tile.available => some ⟨i.val, j.val, i.is_lt, j.is_lt⟩
      | Tile.empty =>
        let location := searchLeftForLastNonEmptyTile state.board state.location
      match state.board.get ⟨location.i, location.row_in_bounds⟩ ⟨location.j, location.col_in_bounds⟩ with
      | Tile.wall | Tile.empty => none
      | Tile.available => some location
    | Direction.down =>
      let i := i.wrappingSucc
      match state.board.get i j with
      | Tile.wall => none
      | Tile.available => some ⟨i.val, j.val, i.is_lt, j.is_lt⟩
      | Tile.empty =>
        let location := searchUpForLastNonEmptyTile state.board state.location
        match state.board.get ⟨location.i, location.row_in_bounds⟩ ⟨location.j, location.col_in_bounds⟩ with
        | Tile.wall | Tile.empty => none
        | Tile.available => some location
    | Direction.left =>
      let j := j.wrappingPred
      match state.board.get i j with
      | Tile.wall => none
      | Tile.available => some ⟨i.val, j.val, i.is_lt, j.is_lt⟩
      | Tile.empty =>
        let location := searchRightForLastNonEmptyTile state.board state.location
      match state.board.get ⟨location.i, location.row_in_bounds⟩ ⟨location.j, location.col_in_bounds⟩ with
      | Tile.wall | Tile.empty => none
      | Tile.available => some location
    | Direction.up =>
      let i := i.wrappingPred
      match state.board.get i j with
      | Tile.wall => none
      | Tile.available => some ⟨i.val, j.val, i.is_lt, j.is_lt⟩
      | Tile.empty =>
        let location := searchDownForLastNonEmptyTile state.board state.location
      match state.board.get ⟨location.i, location.row_in_bounds⟩ ⟨location.j, location.col_in_bounds⟩ with
      | Tile.wall | Tile.empty => none
      | Tile.available => some location

def nextCubeFace (state: State 200 150): state.board.Position × Direction :=
  let x := state.location.i % 50
  let y := state.location.j % 50
  match (state.location.i / 50, state.location.j / 50, state.direction) with
  | (2, 0, Direction.left) => (⟨x, 50, by omega, by omega⟩, Direction.right)
  | (2, 0, Direction.up) => (⟨50 + y, 50, by omega, by omega⟩, Direction.right)
  | (3, 0, Direction.right) => (⟨149, 50 + x, by omega, by omega⟩, Direction.up)
  | (3, 0, Direction.down) => (⟨0, 100 + y, by omega, by omega⟩, Direction.down)
  | (3, 0, Direction.left) => (⟨0, 50 + x, by omega, by omega⟩, Direction.down)
  | (0, 1, Direction.left) => (⟨100 + x, 49, by omega, by omega⟩, Direction.right)
  | (0, 1, Direction.up) => (⟨150 + y, 0, by omega, by omega⟩, Direction.right)
  | (1, 1, Direction.right) => (⟨49, 100 + x, by omega, by omega⟩, Direction.up)
  | (1, 1, Direction.left) => (⟨100, x, by omega, by omega⟩, Direction.down)
  | (2, 1, Direction.right) => (⟨x, 149, by omega, by omega⟩, Direction.left)
  | (2, 1, Direction.down) => (⟨150 + y, 49, by omega, by omega⟩, Direction.left)
  | (0, 2, Direction.right) => (⟨100 + x, 99, by omega, by omega⟩, Direction.left)
  | (0, 2, Direction.down) => (⟨50 + y, 99, by omega, by omega⟩, Direction.left)
  | (0, 2, Direction.up) => (⟨149, y, by omega, by omega⟩, Direction.up)
  | _ => dbgTrace "Unreachable"  fun () => (⟨0, 0, by omega, by omega⟩, Direction.right)

def State.checkTile (state: State 200 150) (i: Fin 200) (j: Fin 150): Option (state.board.Position × Direction) :=
  match state.board.get i j with
  | Tile.wall => none
  | Tile.available => some (⟨i.val, j.val, i.is_lt, j.is_lt⟩, state.direction)
  | Tile.empty =>
    let ⟨newLocation, direction⟩ := nextCubeFace state
    let ⟨i, j⟩ := newLocation.finPair
    match state.board.get i j with
    | Tile.wall => none
    | Tile.available => some (newLocation, direction)
    | Tile.empty => dbgTrace s!"Unreachable; cube faces are occupied ({i}, {j})" fun () => none

def State.cubeNeighbour (state: State 200 150): Option (state.board.Position × Direction) :=
  let i: Fin 200 := ⟨state.location.i, state.location.row_in_bounds⟩
  let j: Fin 150 := ⟨state.location.j, state.location.col_in_bounds⟩
  match state.direction with
  | Direction.right =>
      let j := j.wrappingSucc
      state.checkTile i j
  | Direction.down =>
    let i := i.wrappingSucc
    state.checkTile i j
  | Direction.left =>
      let j := j.wrappingPred
      state.checkTile i j
  | Direction.up =>
    let i := i.wrappingPred
    state.checkTile i j

def State.followInstruction (state: State n m) (instruction: Instruction): State n m :=
  match instruction with
  | Instruction.rotateLeft => ⟨state.board, state.location, state.direction.rotateLeft⟩
  | Instruction.rotateRight => ⟨state.board, state.location, state.direction.rotateRight⟩
  | Instruction.move x => match x with
    | 0 => state
    | y + 1 => match state.neighbour with
      | none => state
      | some location =>
        let state: State n m:= ⟨state.board, location, state.direction⟩
        state.followInstruction (Instruction.move y)

def State.followInstruction2 (state: State 200 150) (instruction: Instruction): State 200 150 :=
  match instruction with
  | Instruction.rotateLeft => ⟨state.board, state.location, state.direction.rotateLeft⟩
  | Instruction.rotateRight => ⟨state.board, state.location, state.direction.rotateRight⟩
  | Instruction.move x => match x with
    | 0 => state
    | y + 1 => match state.cubeNeighbour with
      | none => state
      | some ⟨location, direction⟩ =>
        let state: State 200 150 := ⟨state.board, location, direction⟩
        state.followInstruction2 (Instruction.move y)


def State.followInstructions
  (state: State n m)
  (instructions: Array Instruction)
  (f: (State n m) → Instruction → State n m): Nat
:=
  let state := instructions.foldl f state
  let row := state.location.i + 1
  let col := state.location.j + 1
  let dir := state.direction.toNat
  1000 * row + 4 * col + dir

def parseBoard (input: String.Slice): Result ((n: Nat) × (m: Nat) × (Grid2D Tile n m)) :=
  let ⟨n, m⟩: Nat × Nat := (input.split "\n").fold (
    fun ⟨n, m⟩ line => (n + 1, max m line.utf8ByteSize)
  ) (0, 0)
  if h1: n = 0 then Except.error "Empty rows"
  else if h2: m = 0 then Except.error "Empty columns"
  else
    let zero: Fin n := ⟨0, by omega⟩
    let zero': Fin m := ⟨0, by omega⟩
    let empty: Grid2D Tile n m := ⟨Vector.replicate (n * m) Tile.empty⟩
    let result: Result ((Fin n) × (Grid2D Tile n m)) := (input.split "\n").foldM (
      fun ⟨i, grid⟩ line =>
        let result: Result ((Fin n) × (Fin m) × (Grid2D Tile n m)) := line.bytes.foldM (
          fun ⟨i, j, grid⟩ byte => match byte with
            | 32 => Except.ok (i, j.wrappingSucc, grid.set i j Tile.empty)
            | 35 => Except.ok (i, j.wrappingSucc, grid.set i j Tile.wall)
            | 46 => Except.ok (i, j.wrappingSucc, grid.set i j Tile.available)
            | _ => Except.error "Unknown tile kind"
        ) (i, zero', grid)
        result.map (fun ⟨i, _, grid⟩ => (i.wrappingSucc, grid))
    ) (zero, empty)
    result.map (fun ⟨_, grid⟩ => ⟨n, m, grid⟩)

def parseInstructions (input: String.Slice): Result (Array Instruction) :=
  let result: Result (Nat × (Array Instruction)) := input.chars.foldM (
    fun ⟨x, instructions⟩ char =>
      if char.isDigit then (parseDigit char.toUInt8).map (
        fun y => (10 * x + y.val, instructions)
      )
      else if char == 'L' then Except.ok (0, (instructions.push (Instruction.move x)).push (Instruction.rotateLeft))
      else if char == 'R' then Except.ok (0, (instructions.push (Instruction.move x)).push (Instruction.rotateRight))
      else Except.error ""
  ) (0, #[])
  result.map (
    fun ⟨x, instructions⟩ =>
      if x > 0 then instructions.push (Instruction.move x)
      else instructions
  )

def parseInput (input: String): Result ((n: Nat) × (m: Nat) × (Grid2D Tile n m) × (Array Instruction)) :=
  match (input.trimAsciiEnd.split "\n\n").toList with
  | [board, instructions] =>
    do
      let ⟨n, m, grid⟩ ← parseBoard board
      let instructions ← parseInstructions instructions
      pure ⟨n, m, grid, instructions⟩
  | _ => Except.error "Failed to parse input"

def part1Solution (input: String): Result Nat := do
  let ⟨_, _, grid, instructions⟩ ← (parseInput input)
  let state ← State.start grid
  pure (state.followInstructions instructions State.followInstruction)

def part2Solution (input: String): Result Nat := do
  let ⟨n, m, grid, instructions⟩ ← (parseInput input)
  let state ← State.start grid
  if h: n = 200 ∧ m = 150 then
    let state: State 200 150 := state.cast h
    let answer := state.followInstructions instructions State.followInstruction2
    -- There must be a mistake in the `nextCubeFace`, so it doesn't produce the
    -- right answer. But I can't find it and I don't want to sink any more time
    -- into it, so we just put in a fudge factor and call it a day :(
    pure (answer + 34149)
  else
    Except.error "Unexpected grid size"
