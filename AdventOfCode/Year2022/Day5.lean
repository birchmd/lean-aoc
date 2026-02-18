import AdventOfCode.Common.Result

structure Move where
  count: Nat
  src: Nat
  dst: Nat

def Crate: Type := Char

def Column: Type := List Crate

def CratesState: Type := Array Column

def parseNat(input: String.Slice): Result Nat :=
  match input.toNat? with
  | some n => pure n
  | none => Except.error "Failed to parse Nat"

def parseMove(line: String.Slice): Result Move :=
  match (line.split " ").toList with
  | _ :: count :: _ :: src :: _ :: dst :: [] => do
    let count ← parseNat count
    let src ← parseNat src
    let dst ← parseNat dst
    pure ⟨ count, src - 1, dst - 1 ⟩
  | _ => Except.error "Failed to parse move line"

def parseStateLine(line: String.Slice): Array (Option Crate) :=
  match line.chars.fold foldingFunction (0, none, #[]) with
  | (_, (_, x)) => x
  where foldingFunction (s: Nat × (Option Char) × Array (Option Crate)) (c: Char): Nat × (Option Char )× Array (Option Crate) :=
    match s with
    | (i, (label, acc)) =>
      if i % 4 == 1 then
        (i + 1, if c.isAlpha then some c else none, acc)
      else if i % 4 == 2 then
        (i + 1, label, acc.push label)
      else
        (i + 1, label, acc)

def defaultState(lines: String.Slice): Result (Array (Array Crate)) :=
  let first := (((lines.split "\n").take 1).map parseStateLine).toList
  match first with
  | [] => Except.error "Input is empty!"
  | x :: [] => pure ((Array.finRange x.size).map (fun _ => #[]))
  | _ => Except.error "TODO: should be able to prove this is unreachable due to `take 1`"

def parseState(lines: String.Slice): Result CratesState := do
  let default ← defaultState lines
  let state := ((lines.split "\n").map parseStateLine).fold foldingFunction default
  pure (state.map (fun xs => xs.toList))
  where foldingFunction (s: Array (Array Crate)) (row: Array (Option Crate)): Array (Array Crate) :=
    (s.zip row).map (fun pairs => match pairs with
    | (xs, none) => xs
    | (xs, some c) => xs.push c)

def parseMoves(lines: String.Slice): Result (List Move) :=
  ((lines.split "\n").mapM parseMove).toList

def parseInput(input: String): Result (CratesState × (List Move)) :=
  match (input.trimAsciiEnd.split "\n\n").toList with
  | stateLines :: moveLines :: [] => do
    let state <- parseState stateLines
    let moves <- parseMoves moveLines
    pure (state, moves)
  | _ => Except.error "Expected one blank line between state and moves"

def topMost (s: CratesState): String :=
  String.ofList (s.map (fun xs => xs.headD ' ')).toList

def doMove (moveFn: Nat → Column → Column → Result (Column × Column)) (s: CratesState) (m: Move) : Result CratesState :=
  if h: m.src < s.size ∧ m.dst < s.size then
    do
      let src := s.getInternal m.src (by omega)
      let dst := s.getInternal m.dst (by omega)
      let (src, dst) ← moveFn m.count src dst
      let x := s.set m.src src
      pure (x.set m.dst dst (by
        have same_len: x.size = s.size := by apply Array.size_set
        omega
      ))
  else Except.error "Move index out of bounds"

def part1Mover (n: Nat) (src dst: Column): Result (Column × Column) :=
  match n with
  | 0 => pure (src, dst)
  | m + 1 => match src with
    | [] => Except.error "Moved more elements than exist in the stack!"
    | x :: xs => part1Mover m xs (x :: dst)

def part2Mover (n: Nat) (src dst: Column): Result (Column × Column) :=
  helper n src dst []
  where helper (n: Nat) (src dst acc: Column): Result (Column × Column) :=
  match n with
  | 0 => pure (src, acc.reverse.append dst)
  | m + 1 => match src with
    | [] => Except.error "Moved more elements than exist in the stack!"
    | x :: xs => helper m xs dst (x :: acc)

def solution (input: String) (moveFn: Nat → Column → Column → Result (Column × Column)): String :=
  let result: Result String := do
    let (state, moves) ← parseInput input
    let endState ← moves.foldlM (doMove moveFn) state
    pure (topMost endState)
  match result with
  | Except.ok output => output
  | Except.error e => e

def part1Solution(input: String): String := solution input part1Mover
def part2Solution(input: String): String := solution input part2Mover
