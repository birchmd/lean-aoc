import AdventOfCode.Common.Grid2D
import AdventOfCode.Common.Result
import Std.Data.HashSet

structure TreeCount where
  seen: Std.HashSet (Nat × Nat)
  i: Nat
  j: Nat
  lb: Option (Fin 10)

def TreeCount.empty: TreeCount := ⟨ Std.HashSet.ofList [], 0, 0, none ⟩

def TreeCount.checkedInsert (tc: TreeCount) (digit: Fin 10): TreeCount :=
  match tc.lb with
  | none => ⟨ tc.seen.insert (tc.i, tc.j), tc.i, tc.j, some digit ⟩
  | some bound =>
    if bound < digit then
      ⟨ tc.seen.insert (tc.i, tc.j), tc.i, tc.j, some digit ⟩
    else
      tc

def TreeCount.nextRow (tc: TreeCount): TreeCount := ⟨ tc.seen, tc.i + 1, tc.j, tc.lb ⟩
def TreeCount.nextCol (tc: TreeCount): TreeCount := ⟨ tc.seen, tc.i, tc.j + 1, tc.lb ⟩
def TreeCount.prevRow (tc: TreeCount): TreeCount := ⟨ tc.seen, tc.i - 1, tc.j, tc.lb ⟩
def TreeCount.prevCol (tc: TreeCount): TreeCount := ⟨ tc.seen, tc.i, tc.j - 1, tc.lb ⟩
def TreeCount.resetBound(tc: TreeCount): TreeCount := ⟨ tc.seen, tc.i, tc.j, none ⟩

def countTreesInRow (tc: TreeCount) (row: Grid2D.Row (Fin 10)): TreeCount :=
  let x: TreeCount → (Fin 10) → TreeCount := fun tc digit => (tc.checkedInsert digit).nextCol
  let y: (Fin 10) → TreeCount → TreeCount := fun digit tc => tc.prevCol.checkedInsert digit
  let state: TreeCount := ⟨ tc.seen, row.i, 0, none ⟩
  row.foldr y (row.foldl x state).resetBound

def countTreesInCol (tc: TreeCount) (col: Grid2D.Col (Fin 10)): TreeCount :=
  let x: TreeCount → (Fin 10) → TreeCount := fun tc digit => (tc.checkedInsert digit).nextRow
  let y: (Fin 10) → TreeCount → TreeCount := fun digit tc => tc.prevRow.checkedInsert digit
  let state: TreeCount := ⟨ tc.seen, 0, col.j, none ⟩
  col.foldr y (col.foldl x state).resetBound

-- TODO: seems like there is a lot of code duplication between the
-- various `viewingDistance` functions. Is there a way to unify them?
def viewingDistanceLeft (grid: Grid2D (Fin 10)) (i: Fin grid.nRows) (j: Fin grid.nCols): Nat :=
  if j.val == 0 then
    0
  else
    let bound := grid.get i j
    loop (j.val - 1) (by omega) bound 1
  where loop (j: Nat) (h: j < grid.nCols) (bound: Fin 10) (dist: Nat): Nat :=
    let fj: Fin grid.nCols := ⟨j, h⟩
    match j with
    | 0 => dist
    | Nat.succ jm1 =>
      if bound ≤ grid.get i fj then
        dist
      else loop jm1 (by omega) bound (dist + 1)

def viewingDistanceRight (grid: Grid2D (Fin 10)) (i: Fin grid.nRows) (j: Fin grid.nCols): Nat :=
  if h: j.val + 1 = grid.nCols then
    0
  else
    let bound := grid.get i j
    loop (j.val + 1) (by omega) bound 1
  where loop (j: Nat) (h: j < grid.nCols) (bound: Fin 10) (dist: Nat): Nat :=
    let fj: Fin grid.nCols := ⟨j, h⟩
    if h: j + 1 = grid.nCols then
      dist
    else if bound ≤ grid.get i fj then
      dist
    else
      loop (j + 1) (by omega) bound (dist + 1)

def viewingDistanceUp (grid: Grid2D (Fin 10)) (i: Fin grid.nRows) (j: Fin grid.nCols): Nat :=
  if i.val == 0 then
    0
  else
    let bound := grid.get i j
    loop (i.val - 1) (by omega) bound 1
  where loop (i: Nat) (h: i < grid.nRows) (bound: Fin 10) (dist: Nat): Nat :=
    let fi: Fin grid.nRows := ⟨i, h⟩
    match i with
    | 0 => dist
    | Nat.succ im1 =>
      if bound ≤ grid.get fi j then
        dist
      else loop im1 (by omega) bound (dist + 1)

def viewingDistanceDown (grid: Grid2D (Fin 10)) (i: Fin grid.nRows) (j: Fin grid.nCols): Nat :=
  if h: i.val + 1 = grid.nRows then
    0
  else
    let bound := grid.get i j
    loop (i.val + 1) (by omega) bound 1
  where loop (i: Nat) (h: i < grid.nRows) (bound: Fin 10) (dist: Nat): Nat :=
    let fi: Fin grid.nRows := ⟨i, h⟩
    if h: i + 1 = grid.nRows then
      dist
    else if bound ≤ grid.get fi j then
      dist
    else
      loop (i + 1) (by omega) bound (dist + 1)

def part1Solution(input: String): Result Nat :=
  let grid := parseDigitGrid input
  grid.map ( fun grid =>
    let tc :=  grid.foldCols countTreesInCol (grid.foldRows countTreesInRow TreeCount.empty)
    tc.seen.size
  )

def part2Solution(input: String): Result Nat :=
  let grid := parseDigitGrid input
  grid.map ( fun grid =>
    Fin.foldl grid.nRows (
      fun acc i =>
        Fin.foldl grid.nCols (
          fun acc j =>
            let a := viewingDistanceDown grid i j
            let b := viewingDistanceLeft grid i j
            let c := viewingDistanceRight grid i j
            let d := viewingDistanceUp grid i j
            let score := a * b * c * d
            max acc score
        ) acc
    ) 0
  )

-- Basic relations between the `TreeCount` modifying functions
theorem next_row_prev_row_id (tc: TreeCount): tc.nextRow.prevRow.i = tc.i := by rfl
theorem next_row_col_unchanged (tc: TreeCount): tc.nextRow.j = tc.j := by rfl
theorem next_col_prev_col_id (tc: TreeCount): tc.nextCol.prevCol.j = tc.j := by rfl
theorem next_col_row_unchanged (tc: TreeCount): tc.nextCol.i = tc.i := by rfl
