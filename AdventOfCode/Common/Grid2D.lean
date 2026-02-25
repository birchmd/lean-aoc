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

structure Grid2D.Position (grid: Grid2D α) where
  i: Nat
  j: Nat
  row_in_bounds: i < grid.nRows
  col_in_bounds: j < grid.nCols

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

def parseGrid (parser: UInt8 → Result α) (input: String): Result (Grid2D α) :=
  let slice := input.trimAscii
  let nCols := ((slice.find? "\n").map (fun p => p.offset.byteIdx)).getD slice.utf8ByteSize
  let bytesArrResult := ((slice.bytes.filter (fun b => b != newLine!)).mapM parser).toArray
  bytesArrResult >>= ( fun bytesArr =>
    let nRows := bytesArr.size / nCols
    if correct_size: bytesArr.size = nRows * nCols then
      let inner: Vector α (nRows * nCols) := ⟨ bytesArr, correct_size ⟩
      pure ⟨ nRows, nCols, inner ⟩
    else
      Except.error "Input size is not a rectangular grid"
  )

def parseDigitGrid (input: String): Result (Grid2D (Fin 10)) := parseGrid parseDigit input

-- Theorem proving if the row index and column index are in bounds then
-- the index into the linearized array is also in bounds.
theorem index_in_bounds (i j n m : Nat) (row_in_bounds: i < n) (col_in_bounds: j < m): i * m + j < n * m := by
  have h1: (i + 1) * m = i * m + m := by rw [Nat.add_mul, Nat.one_mul]
  have h2: i + 1 ≤ n := by omega
  have h3: m ≤ m := by omega
  have h4: (i + 1) * m ≤ n * m := Nat.mul_le_mul h2 h3
  omega

-- Theorem proving if the index of the linearized array is in bounds then
-- we can get a row index that is in bounds by dividing by the number of columns.
theorem row_in_bounds (i n m: Nat) (m_not_zero: 0 < m) (i_lt: i < n * m): i / m < n := by
  have h1: m ∣ (n * m) := Nat.dvd_mul_left m n
  have h2: i / m < (n * m) / m := Nat.div_lt_div_of_lt_of_dvd h1 i_lt
  rw [Nat.mul_div_cancel n m_not_zero] at h2
  exact h2

-- If we have an element of `Fin n` then `n` cannot be zero.
theorem have_index_means_non_empty (index: Fin n): 0 < n := by
  let m := index.val
  have h1: m < n := index.is_lt
  have h2: 0 ≤ m := Nat.zero_le m
  omega

-- Convert a linearized index into a row, column pair.
def lin_index_to_row_col (index: Fin (n * m)): (Fin n) × (Fin m) :=
  have h1: 0 < n * m := have_index_means_non_empty index
  have h2: 0 < m := by grind
  let i := ⟨index / m, row_in_bounds index n m h2 index.is_lt⟩
  let j := ⟨index % m, Nat.mod_lt index h2⟩
  (i, j)

def Grid2D.get (grid: Grid2D α) (i: Fin grid.nRows) (j: Fin grid.nCols): α :=
    let index := i.val * grid.nCols + j.val
    have h := index_in_bounds i.val j.val grid.nRows grid.nCols i.isLt j.isLt
    grid.inner[index]

def Grid2D.Position.get {grid: Grid2D α} (p: grid.Position): α :=
  grid.get ⟨p.i, p.row_in_bounds⟩ ⟨p.j, p.col_in_bounds⟩

def Grid2D.Position.neighbors {grid: Grid2D α} (p: grid.Position): Array (grid.Position) :=
  let ⟨l, r⟩ := predSucc ⟨p.i, p.row_in_bounds⟩
  let ⟨u, d⟩ := predSucc ⟨p.j, p.col_in_bounds⟩
  let lr := #[l, r].filterMap (fun x => x)
  let ud := #[u, d].filterMap (fun x => x)
  let x: Array grid.Position := lr.map (fun i => ⟨i.val, p.j, i.is_lt, p.col_in_bounds⟩)
  let y: Array grid.Position := ud.map (fun j => ⟨p.i, j.val, p.row_in_bounds, j.is_lt⟩)
  x ++ y
  where predSucc {n: Nat} (x: Fin n): (Option (Fin n)) × (Option (Fin n)) :=
    have h1: x.val.pred ≤ x.val := Nat.pred_le x.val
    let left := if x.val = 0 then none else some ⟨x.val.pred, by omega⟩
    let right := if h: x.val < n - 1 then some ⟨x + 1, by omega⟩ else none
    (left, right)

def Grid2D.Position.finPair {grid: Grid2D α} (p: grid.Position): (Fin grid.nRows) × (Fin grid.nCols) :=
  (⟨p.i, p.row_in_bounds⟩, ⟨p.j, p.col_in_bounds⟩)

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

def Grid2D.find? (grid: Grid2D α) (f: α → Bool): Option (grid.Position) := do
  let index ← grid.inner.findFinIdx? f
  let ⟨i, j⟩ := lin_index_to_row_col index
  pure ⟨i.val, j.val, i.is_lt, j.is_lt⟩
