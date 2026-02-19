import AdventOfCode.Common.Result

notation (name := newLine) "newLine!" => 10
notation (name := zeroDigit) "zeroDigit!" => 48
notation (name := nineDigit) "nineDigit!" => 57

structure Grid2D α where
  nRows: Nat
  nCols: Nat
  inner: Vector α (nRows * nCols)

instance [ToString α] : ToString (Grid2D α) where
  toString grid := s!"Grid ({grid.nRows}x{grid.nCols}) {grid.inner.toArray}"

structure Grid2D.Col α where
  grid: Grid2D α
  j: Nat
  col_in_bounds: j < grid.nCols

structure Grid2D.Row α where
  grid: Grid2D α
  i: Nat
  row_in_bounds: i < grid.nRows

def parseDigit (byte: UInt8): Result (Fin 10) :=
  let x := byte.toNat
  if h: zeroDigit! ≤ x ∧ x ≤ nineDigit! then
    Except.ok ⟨ x - zeroDigit!, (by omega) ⟩
  else
    Except.error s!"Given byte {byte} is not a digit"

def parseDigitGrid (input: String): Result (Grid2D (Fin 10)) :=
  let slice := input.trimAscii
  let nCols := ((slice.find? "\n").map (fun p => p.offset.byteIdx)).getD slice.utf8ByteSize
  let bytesArrResult := ((slice.bytes.filter (fun b => b != newLine!)).mapM parseDigit).toArray
  bytesArrResult >>= ( fun bytesArr =>
    let nRows := bytesArr.size / nCols
    if correct_size: bytesArr.size = nRows * nCols then
      let inner: Vector (Fin 10) (nRows * nCols) := ⟨ bytesArr, correct_size ⟩
      pure ⟨ nRows, nCols, inner ⟩
    else
      Except.error "Input size is not a rectangular grid"
  )

-- Theorem proving if the row index and column index are in bounds then
-- the index into the linearized array is also in bounds.
theorem index_in_bounds (i j n m : Nat) (row_in_bounds: i < n) (col_in_bounds: j < m): i * m + j < n * m := by
  have h1: (i + 1) * m = i * m + m := by rw [Nat.add_mul, Nat.one_mul]
  have h2: i + 1 ≤ n := by omega
  have h3: m ≤ m := by omega
  have h4: (i + 1) * m ≤ n * m := Nat.mul_le_mul h2 h3
  omega

def Grid2D.get (grid: Grid2D α) (i: Fin grid.nRows) (j: Fin grid.nCols): α :=
    let index := i.val * grid.nCols + j.val
    have h := index_in_bounds i.val j.val grid.nRows grid.nCols i.isLt j.isLt
    grid.inner[index]

def Grid2D.row (grid: Grid2D α) (i: Nat) (row_in_bounds: i < grid.nRows): Grid2D.Row α :=
  ⟨ grid, i, row_in_bounds ⟩

def Grid2D.col (grid: Grid2D α) (j: Nat) (col_in_bounds: j < grid.nCols): Grid2D.Col α :=
  ⟨ grid, j, col_in_bounds ⟩

def Grid2D.Row.foldl (row: Grid2D.Row α) (f: β → α → β) (init: β): β :=
  let grid := row.grid
  let start := row.i * grid.nCols
  let stop := start + grid.nCols
  let subarray := grid.inner.toArray.toSubarray start stop
  subarray.foldl f init

def Grid2D.Col.foldl (col: Grid2D.Col α) (f: β → α → β) (init: β): β :=
  Fin.foldl col.grid.nRows loop init
  where loop (acc: β) (i: Fin col.grid.nRows): β :=
    let index := i.val * col.grid.nCols + col.j
    have h := index_in_bounds i.val col.j col.grid.nRows col.grid.nCols i.isLt col.col_in_bounds
    let el := col.grid.inner[index]
    (f acc el)

def Grid2D.Row.foldr (row: Grid2D.Row α) (f: α → β → β) (init: β): β :=
  let grid := row.grid
  let start := row.i * grid.nCols
  let stop := start + grid.nCols
  let subarray := grid.inner.toArray.toSubarray start stop
  subarray.foldr f init

def Grid2D.Col.foldr (col: Grid2D.Col α) (f: α → β → β) (init: β): β :=
  Fin.foldr col.grid.nRows loop init
  where loop (i: Fin col.grid.nRows) (acc: β): β :=
    let index := i.val * col.grid.nCols + col.j
    have h := index_in_bounds i.val col.j col.grid.nRows col.grid.nCols i.isLt col.col_in_bounds
    let el := col.grid.inner[index]
    (f el acc)

def Grid2D.foldRows (grid: Grid2D α) (f: β → Grid2D.Row α → β) (init: β): β :=
  Fin.foldl grid.nRows loop init
  where loop (acc: β) (i: Fin grid.nRows): β :=
    let row := grid.row i.val i.isLt
    (f acc row)

def Grid2D.foldCols (grid: Grid2D α) (f: β → Grid2D.Col α → β) (init: β): β :=
  Fin.foldl grid.nCols loop init
  where loop (acc: β) (j: Fin grid.nCols): β :=
    let col := grid.col j.val j.isLt
    (f acc col)
