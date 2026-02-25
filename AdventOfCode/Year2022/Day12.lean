import AdventOfCode.Common.Grid2D
import AdventOfCode.Common.Result
import Std.Data.HashSet

notation (name := upperE) "upperE!" => 69
notation (name := upperS) "upperS!" => 83
notation (name := lowerA) "lowerA!" => 97
notation (name := lowerZ) "lowerZ!" => 122

inductive Elevation where
  | Start: Elevation
  | value (h: Fin 26): Elevation
  | End: Elevation

def Elevation.height (e: Elevation) : Fin 26 :=
  match e with
  | Elevation.Start => 0
  | Elevation.value h => h
  | Elevation.End => 25

def Elevation.isStart (e: Elevation) : Bool :=
  match e with
  | Elevation.Start => true
  | Elevation.End | Elevation.value _ => false

def Elevation.isEnd (e: Elevation) : Bool :=
  match e with
  | Elevation.End => true
  | Elevation.Start | Elevation.value _ => false

def parseElevation (byte: UInt8): Result Elevation :=
  let n := byte.toNat
  if h: lowerA! ≤ n ∧ n ≤ lowerZ! then
    Except.ok (Elevation.value ⟨n - lowerA!, by omega⟩)
  else if n == upperE! then
    Except.ok Elevation.End
  else if n == upperS! then
    Except.ok Elevation.Start
  else
    Except.error "Unknown height"

def parseElevationGrid (input: String): Result (Grid2D Elevation) := parseGrid parseElevation input

structure BfsState where
  grid: Grid2D Elevation
  visited: Std.HashSet ((Fin grid.nRows) × Fin (grid.nCols))
  queue: Std.Queue (Nat × grid.Position)
  -- TODO: this is only used to show termination of the `bfs` function.
  -- But it should not be needed because `bfs` does terminate since
  -- eventually the queue will be empty and every space will have been visited.
  -- How can we prove this to Lean?
  bound: Nat

def startStateAt (f: Elevation → Bool) (grid: Grid2D Elevation): Result BfsState :=
  match grid.find? f with
  | some position =>
    let queue := Std.Queue.empty
    Except.ok ⟨grid, Std.HashSet.ofList [], queue.enqueue (0, position), 4 * grid.nRows * grid.nCols⟩
  | none => Except.error "Start not found!"

def bfs (state: BfsState) (isNeighbor: state.grid.Position → state.grid.Position → Bool) (condition: state.grid.Position → Bool): Result Nat :=
  if state.bound = 0 then Except.error "BFS hit iteration bound"
  else
    do
      let ⟨⟨nSteps, position⟩, queue⟩ ← getOrErr state.queue.dequeue? "BFS failed to find"
      let pair := position.finPair
      if state.visited.contains pair then
        bfs ⟨state.grid, state.visited, queue, state.bound - 1⟩ isNeighbor condition
      else
        let visited := state.visited.insert pair
        if condition position then Except.ok nSteps
        else
          let queue := position.neighbors.foldl (enqueueNeighbors (isNeighbor position) (nSteps + 1) visited) queue
          bfs ⟨state.grid, visited, queue, state.bound - 1⟩ isNeighbor condition
  termination_by state.bound
  where enqueueNeighbors {grid: Grid2D Elevation} (isNeighbor: grid.Position → Bool) (steps: Nat) (visited: Std.HashSet ((Fin grid.nRows) × Fin (grid.nCols))) (queue: Std.Queue (Nat × grid.Position)) (position: grid.Position): Std.Queue (Nat × grid.Position) :=
    if visited.contains position.finPair then queue
    else if isNeighbor position then queue.enqueue (steps, position)
    else queue

def isNeighbor {grid: Grid2D Elevation} (src: grid.Position) (dst: grid.Position): Bool :=
    dst.get.height.val ≤ src.get.height.val + 1

def part1Solution(input: String): Result Nat := do
  let grid ← parseElevationGrid input
  let state ← startStateAt Elevation.isStart grid
  bfs state isNeighbor (fun p => p.get.isEnd)

def part2Solution(input: String): Result Nat := do
  let grid ← parseElevationGrid input
  -- Run the BFS backwards by starting at the end and reversing
  -- the  neighbor check.
  let state ← startStateAt Elevation.isEnd grid
  bfs state (fun src dst => isNeighbor dst src) (fun p => p.get.height = 0)
