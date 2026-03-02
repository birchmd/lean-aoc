import AdventOfCode.Common.Result
import AdventOfCode.Common.Grid2D
import Std.Data.HashMap
import Std.Data.HashSet

structure Cave (n: Nat) where
  flowRates: Vector Nat n
  distances: Grid2D Nat n n
  neighbours: Vector (Array (Fin n)) n

def Cave.default (n: Nat): Cave n :=
  let grid: Grid2D Nat n n := ⟨Vector.replicate (n * n) (2 * n)⟩
  ⟨Vector.replicate n 0, grid, Vector.replicate n #[]⟩

def countAndEnumerate(state: Nat × (Std.HashMap String.Slice Nat)) (line: String.Slice): Result (Nat × (Std.HashMap String.Slice Nat)) :=
  let ⟨n, indices⟩ := state
  match (((line.split " ").drop 1).take 1).toList with
  | label :: [] => Except.ok ⟨n + 1, indices.insert label n⟩
  | _ => Except.error "Failed to parse label"

def parseLine(n: Nat) (indices: Std.HashMap String.Slice Nat) (line: String.Slice): Result (Nat × (Array (Fin n))) :=
  let tokens: List String.Slice := (line.split " ").toList
  let rate := match tokens.find? (fun p => p.contains "=") with
    | none => Except.error "Failed to find rate"
    | some token => getOrErr ((token.dropPrefix "rate=").dropSuffix ";").toNat? "Failed to parse rate"
  let neighbours: Result (Array (Fin n)) := match tokens.dropWhile (fun x: String.Slice => ¬x.startsWith "valve") with
    | [] => Except.error s!"Failed to find neighbours in {line}"
    | _ :: tail =>
      let ns := tail.iter.mapM (
        fun label => match indices.get? (label.dropSuffix ",") with
          | none => Except.error s!"Unknown label {label}"
          | some index => if h: index < n then Except.ok ⟨index, h⟩ else Except.error "Index too large"
      )
      ns.toArray
  do
    let r ← rate
    let ns ← neighbours
    pure ⟨r, ns⟩

def wrappingSucc (i: Fin n): Fin n :=
  let j := i.val + 1
  if h: j < n then ⟨j, h⟩
  else ⟨0, have_index_means_non_empty i⟩

def buildCave (indices: Std.HashMap String.Slice Nat) (state: (Fin n) × (Cave n)) (line: String.Slice): Result ((Fin n) × (Cave n)):=
  let ⟨i, cave⟩ := state
  (parseLine n indices line).map (
    fun ⟨rate, ns⟩ =>
      let cave: Cave n := ⟨cave.flowRates.set i rate, cave.distances, cave.neighbours.set i ns⟩
      ⟨wrappingSucc i, cave⟩
  )

def fillDistances (cave: Cave n): Cave n :=
  let distances := Fin.foldl n (fun acc i => acc.set i i 0) cave.distances
  let distances := Fin.foldl n (
    fun acc i =>
      let queue := (cave.neighbours.get i).foldl (fun q x => q.enqueue (1, x)) Std.Queue.empty
      loop acc cave.neighbours i queue (2 * n)
  ) distances
  ⟨cave.flowRates, distances, cave.neighbours⟩
  where loop {n: Nat} (acc: Grid2D Nat n n) (neighbours: Vector (Array (Fin n)) n) (i: Fin n) (queue: Std.Queue (Nat × (Fin n))) (bound: Nat): Grid2D Nat n n :=
    if bound = 0 then acc
    else match queue.dequeue? with
    | none => acc
    | some ⟨⟨s, j⟩, queue⟩ =>
      if acc.get i j ≤ n then loop acc neighbours i queue (bound - 1)
      else
        let acc := acc.set i j s
        let queue := (neighbours.get j).foldl (
          fun q j =>
            if n < acc.get i j then q.enqueue (s + 1, j)
            else q
        ) queue
        loop acc neighbours i queue (bound - 1)

def parseInput (input: String): Result ((n: Nat) × Cave n × (Fin n)) := do
  let trimmed := input.trimAscii
  let ⟨n, indices⟩ ← (trimmed.split "\n").foldM countAndEnumerate ⟨0, Std.HashMap.ofList []⟩
  if h: n = 0 then Except.error "Empty input"
  else
    let ⟨_, cave⟩ ← (trimmed.split "\n").foldM (buildCave indices) ⟨⟨0, by omega⟩, Cave.default n⟩
    let cave := fillDistances cave
    let startIndex ← getOrErr (indices.get? "AA") "Failed to find AA label"
    let startIndex ← if h: startIndex < n then Except.ok ⟨startIndex, h⟩ else Except.error "AA Index too big"
    Except.ok ⟨n, cave, startIndex⟩

-- State used in searching for the optimal path in part 1.
structure State (n: Nat) where
  visited: Std.HashSet (Fin n)
  flow: Nat
  pos: Fin n
  time: Nat

partial def bfs (cave: Cave n) (best: Nat) (queue: Std.Queue (State n)) : Nat :=
  match queue.dequeue? with
  | none => best
  | some ⟨state, queue⟩ =>
    if state.time = 0 then
      let newBest := max state.flow best
      bfs cave newBest queue
    else
      let visited := state.visited.insert state.pos
      let newFlow := state.flow + state.time * (cave.flowRates.get state.pos)
      let newBest := max newFlow best
      let queue := Fin.foldl n (
        fun q j =>
          if visited.contains j then q
          else if cave.flowRates.get j = 0 then q
          else
            let remainingTime := state.time - (cave.distances.get state.pos j) - 1
            let newState: State n := ⟨visited, newFlow, j, remainingTime⟩
            q.enqueue newState
      ) queue
      bfs cave newBest queue

-- Structures used in searching for the optimal path in part 2
inductive Position (n: Nat) where
  | Arrived (x y: Fin n): Position n
  | Going (x y: Fin n) (dt: Nat): Position n

structure State2 (n: Nat) where
  visited: Std.HashSet (Fin n)
  flow: Nat
  pos: Position n
  time: Nat

inductive MaybeModified α where
  | Unchanged (x: α): MaybeModified α
  | Modified (x: α): MaybeModified α

def MaybeModified.modify (mm: MaybeModified α) (f: α → α): MaybeModified α :=
  match mm with
  | Unchanged x => MaybeModified.Modified (f x)
  | Modified x => MaybeModified.Modified (f x)

partial def bfs2 (cave: Cave n) (best: Nat) (queue: Std.Queue (State2 n)) : Nat :=
  match queue.dequeue? with
  | none => best
  | some ⟨state, queue⟩ =>
    if state.time = 0 then
      let newBest := max state.flow best
      bfs2 cave newBest queue
    else match state.pos with
    | Position.Arrived x y =>
      let visited := (state.visited.insert x).insert y
      let newFlow := state.flow + state.time * ((cave.flowRates.get x) + (cave.flowRates.get y))
      let newBest := max newFlow best
      let queue := Fin.foldl n (
        fun q j =>
          if visited.contains j then q
          else if cave.flowRates.get j = 0 then q
          else Fin.foldl n (
              fun q k =>
                if visited.contains k then q
                else if cave.flowRates.get k = 0 then q
                else if k = j then q
                else
                  let dj := cave.distances.get x j + 1
                  let dk := cave.distances.get y k + 1
                  let ⟨newPos, remainingTime⟩: Position n × Nat := if dj = dk then
                    ⟨Position.Arrived j k, state.time - dj⟩
                  else if dj < dk then
                    ⟨Position.Going j k (dk - dj), state.time - dj⟩
                  else
                    ⟨Position.Going k j (dj - dk), state.time - dk⟩
                  -- Try to prune off bad paths with an upper bound
                  -- on how good the rest of it can be relative to
                  -- the current best
                  let bound := Fin.foldl n (
                    fun acc i =>
                      if visited.contains i then acc
                      else acc + remainingTime * cave.flowRates.get i
                  ) newFlow
                  if bound < newBest then q
                  else
                    let newState: State2 n := ⟨visited, newFlow, newPos, remainingTime⟩
                    q.enqueue newState
            ) q
      ) queue
      bfs2 cave newBest queue
    | Position.Going x y dt =>
      let visited := state.visited.insert x
      let newFlow := state.flow + state.time * (cave.flowRates.get x)
      let newBest := max newFlow best
      let queue := Fin.foldl n (
        fun q j =>
          if visited.contains j then q
          else if cave.flowRates.get j = 0 then q
          else if j = y then q
          else
            let dj := cave.distances.get x j + 1
            let ⟨newPos, remainingTime⟩: Position n × Nat := if dj = dt then
              ⟨Position.Arrived j y, state.time - dj⟩
            else if dj < dt then
              ⟨Position.Going j y (dt - dj), state.time - dj⟩
            else
              ⟨Position.Going y j (dj - dt), state.time - dt⟩
            -- Early pruning here too.
            let bound := Fin.foldl n (
              fun acc i =>
                if visited.contains i then acc
                else acc + remainingTime * cave.flowRates.get i
            ) newFlow
            if bound < newBest then q
            else
              let newState: State2 n := ⟨visited, newFlow, newPos, remainingTime⟩
              q.modify (fun x => x.enqueue newState)
      ) (MaybeModified.Unchanged queue)
      let ⟨newBest, queue⟩ := match queue with
        | MaybeModified.Unchanged q =>
          -- Make sure we still resolve the last spot not reached
          let newFlow := newFlow + (state.time - dt) * (cave.flowRates.get y)
          let newBest := max newFlow best
          (newBest, q)
        | MaybeModified.Modified q => (newBest, q)
      bfs2 cave newBest queue

def part1Solution(input: String): Result Nat := do
  let ⟨n, cave, startIndex⟩ ← parseInput input
  let state: State n := ⟨Std.HashSet.ofList [], 0, startIndex, 30⟩
  pure (bfs cave 0 (Std.Queue.empty.enqueue state))

def part2Solution(input: String): Result Nat := do
  let ⟨n, cave, startIndex⟩ ← parseInput input
  let start := Position.Arrived startIndex startIndex
  let state: State2 n := ⟨Std.HashSet.ofList [], 0, start, 26⟩
  pure (bfs2 cave 0 (Std.Queue.empty.enqueue state))
