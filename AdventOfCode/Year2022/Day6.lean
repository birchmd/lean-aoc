import Init.Data.Vector

-- Theorems needed throughout the program.
-- They prove things like the string slicing is correct
-- and the algorithm terminates.

-- All characters have a positive size in bytes.
theorem chars_not_zero (c: Char): c.utf8Size > 0 := by
  have := Char.utf8Size_eq c
  omega

-- Any String Slice position that is not the end must be strictly before then end.
theorem lt_end {s: String.Slice} {p: String.Slice.Pos s} (h: p ≠ s.endPos): p < s.endPos := by
  have e_le_end: p ≤ s.endPos := String.Slice.Pos.le_endPos p
  simp [String.Slice.Pos.ext_iff, String.Pos.Raw.ext_iff] at h
  simp [String.Slice.Pos.le_iff, String.Pos.Raw.le_iff] at e_le_end
  simp [String.Slice.Pos.lt_iff, String.Pos.Raw.lt_iff]
  omega

-- If a String Slice position is not at the end then the next position
-- is closer to the end of the Slice.
theorem pos_decreasing {s: String.Slice} {p: String.Slice.Pos s} (h: p ≠ s.endPos): s.utf8ByteSize - (p.next h).offset.byteIdx < s.utf8ByteSize - p.offset.byteIdx := by
  simp
  have non_zero_move: (p.get h).utf8Size > 0 := chars_not_zero (p.get h)
  have not_at_end_yet: p.offset.byteIdx < s.utf8ByteSize := by
    have e_lt_end: p < s.endPos := lt_end h
    simp_all [String.Slice.Pos.lt_iff, String.Pos.Raw.lt_iff]
  omega

-- Given String Slice positions a, b, c, if a ≤ b ∧ b < c then a < c.
theorem pos_le_lt_trans {s: String.Slice} (a b c: String.Slice.Pos s) (h1: a ≤ b) (h2: b < c): a < c := by
  simp [String.Slice.Pos.le_iff, String.Pos.Raw.le_iff] at h1
  simp_all [String.Slice.Pos.lt_iff, String.Pos.Raw.lt_iff]
  omega

-- Given String Slice positions a, b, c, if a < b ∧ b ≤ c then a < c.
theorem pos_lt_le_trans {s: String.Slice} (a b c: String.Slice.Pos s) (h1: a < b) (h2: b ≤ c): a < c := by
  simp [String.Slice.Pos.le_iff, String.Pos.Raw.le_iff] at h2
  simp_all [String.Slice.Pos.lt_iff, String.Pos.Raw.lt_iff]
  omega

-- Given String Slice positions p, q, if p < q ∧ q ≠ s.endPos then p.next < q.next.
theorem next_lt {s: String.Slice} {p q: String.Slice.Pos s} (hlt: p < q) (h_q_ne: q ≠ s.endPos): (p.next (String.Slice.Pos.ne_endPos_of_lt hlt)) < (q.next h_q_ne) := by
  have h_p_ne: p ≠ s.endPos := String.Slice.Pos.ne_endPos_of_lt hlt
  let next_p := p.next h_p_ne
  let next_q := q.next h_q_ne
  have next_p_le_q: next_p ≤ q := String.Slice.Pos.next_le_of_lt hlt
  have q_lt_next_q: q < next_q := String.Slice.Pos.lt_next
  exact pos_le_lt_trans next_p q next_q next_p_le_q q_lt_next_q

-- End of theorems.

def CountsVec: Type := Vector Nat 256

def allDistinct (counts: CountsVec): Bool :=
  counts.all (fun n => n ≤ 1)

def insert (counts: CountsVec) (x: UInt8): CountsVec :=
  let x := x.toFin
  let n := counts.get x
  counts.set x (n + 1)

def remove (counts: CountsVec) (x: UInt8): CountsVec :=
  let x := x.toFin
  let n := counts.get x
  counts.set x (n - 1)

def slidingWindow {slice: String.Slice} (s e : String.Slice.Pos slice) (counts: CountsVec) (s_lt_e: s < e): Option Nat :=
  if allDistinct counts then
    some (e.offset.byteIdx)
  else if e_not_end: e ≠ slice.endPos then
    let s_not_end: s ≠ slice.endPos := String.Slice.Pos.ne_endPos_of_lt s_lt_e
    let counts := remove counts (s.byte s_not_end)
    let counts := insert counts (e.byte e_not_end)
    let new_e := e.next e_not_end
    let new_s := s.next s_not_end
    let new_s_lt_e: new_s < new_e := next_lt s_lt_e e_not_end
    slidingWindow new_s new_e counts new_s_lt_e
  else none
termination_by slice.endPos.offset.byteIdx - e.offset.byteIdx
decreasing_by
  exact pos_decreasing e_not_end

def solution (input: String) (window_size: Nat): Nat :=
  let slice := input.sliceTo input.endPos
  let s := slice.startPos
  if input.length < window_size then 0
  else if s_not_end: s ≠ slice.endPos then
    let s2 := s.next s_not_end
    let e := s2.nextn (window_size - 1)
    let counts: CountsVec := (slice.sliceTo e).bytes.fold insert (Vector.replicate 256 0)
    let s_lt_e: s < e := pos_lt_le_trans s s2 e String.Slice.Pos.lt_next String.Slice.Pos.le_nextn
    let result := slidingWindow s e counts s_lt_e
    result.getD 0
  else 0

def part1Solution(input: String): Nat := solution input 4
def part2Solution(input: String): Nat := solution input 14
