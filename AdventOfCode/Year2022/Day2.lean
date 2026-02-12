import Batteries.Data.List

inductive Move where
  | Rock : Move
  | Paper : Move
  | Scissors : Move

inductive Outcome where
  | Win : Outcome
  | Lose : Outcome
  | Draw : Outcome

def parseMove(s: String.Slice): Option Move :=
  match s.toString with
  | "A" | "X" => some Move.Rock
  | "B" | "Y" => some Move.Paper
  | "C" | "Z" => some Move.Scissors
  | _ => none

def parseOutcome(s: String.Slice): Option Outcome :=
  match s.toString with
  | "X" => some Outcome.Lose
  | "Y" => some Outcome.Draw
  | "Z" => some Outcome.Win
  | _ => none

def moveScore(m: Move): Nat :=
  match m with
  | Move.Rock => 1
  | Move.Paper => 2
  | Move.Scissors => 3

def outcomeScore(x: Outcome): Nat :=
  match x with
  | Outcome.Win => 6
  | Outcome.Lose => 0
  | Outcome.Draw => 3

def roundOutcome(opp me: Move): Outcome :=
  match opp, me with
  | Move.Rock, Move.Rock => Outcome.Draw
  | Move.Rock, Move.Paper => Outcome.Win
  | Move.Rock, Move.Scissors => Outcome.Lose
  | Move.Paper, Move.Rock => Outcome.Lose
  | Move.Paper, Move.Paper => Outcome.Draw
  | Move.Paper, Move.Scissors => Outcome.Win
  | Move.Scissors, Move.Rock => Outcome.Win
  | Move.Scissors, Move.Paper => Outcome.Lose
  | Move.Scissors, Move.Scissors => Outcome.Draw

def chooseMove(opp: Move) (outcome: Outcome): Move :=
  match opp, outcome with
  | Move.Rock, Outcome.Lose => Move.Scissors
  | Move.Rock, Outcome.Draw => Move.Rock
  | Move.Rock, Outcome.Win => Move.Paper
  | Move.Paper, Outcome.Lose => Move.Rock
  | Move.Paper, Outcome.Draw => Move.Paper
  | Move.Paper, Outcome.Win => Move.Scissors
  | Move.Scissors, Outcome.Lose => Move.Paper
  | Move.Scissors, Outcome.Draw => Move.Scissors
  | Move.Scissors, Outcome.Win => Move.Rock

def roundScore(opp me: Move): Nat :=
  (moveScore me) + outcomeScore (roundOutcome opp me)

def totalScore(rounds: List (Move × Move)): Nat :=
  rounds.foldl (fun acc (opp, me) => acc + roundScore opp me) 0

def parseLine(line: String.Slice): Option (Move × Move) :=
  match (line.split " ").toList with
  | x :: y :: [] => do
    let m <- parseMove x
    let n <- parseMove y
    (m, n)
  | _ => none

def parseLine2(line: String.Slice): Option (Move × Outcome) :=
  match (line.split " ").toList with
  | x :: y :: [] => do
    let m <- parseMove x
    let o <- parseOutcome y
    (m, o)
  | _ => none

def parseInput (parseLine: String.Slice → Option α) (input: String): List α :=
  ((input.trimAscii.split "\n").map parseLine).toList.allSome.getD []

def part1Solution (input: String): Nat := input
  |> (parseInput parseLine)
  |> totalScore

def part2Solution (input: String): Nat := input
  |> (parseInput parseLine2)
  |> mapChooseMove
  |> totalScore
  where mapChooseMove(input: List (Move × Outcome)): List (Move × Move) :=
    input.map (fun (m, o) => (m, chooseMove m o))

-- Theorems showing `roundOutcome` is implemented correctly
theorem equal_moves_draw(m: Move): roundOutcome m m = Outcome.Draw := by
  cases m <;> simp [roundOutcome]

theorem rps_anti_symm (m n: Move) (pf: roundOutcome m n = Outcome.Win): roundOutcome n m = Outcome.Lose := by
  cases m <;> cases n <;> simp [roundOutcome] at pf ⊢

theorem rock_defeats_scissors: roundOutcome Move.Scissors Move.Rock = Outcome.Win := by rfl
theorem scissors_defeats_paper: roundOutcome Move.Paper Move.Scissors = Outcome.Win := by rfl
theorem paper_defeats_rock: roundOutcome Move.Rock Move.Paper = Outcome.Win := by rfl

-- Theorem showing `chooseMove` is implemented correctly
theorem correct_outcome(m: Move) (outcome: Outcome): roundOutcome m (chooseMove m outcome) = outcome := by
  cases m <;> cases outcome <;> simp [chooseMove, roundOutcome]
