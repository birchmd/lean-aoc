notation (name := capitalA) "capitalA!" => 65
notation (name := capitalZ) "capitalZ!" => 90
notation (name := lowerA) "lowerA!" => 97
notation (name := lowerZ) "lowerZ!" => 122

def u64Max: UInt64 := UInt64.ofFin ⟨UInt64.size - 1, (by decide)⟩

-- Map bytes in 'a' - 'z' to range 1-26
-- Map bytes in 'A' - 'Z' to range 27-52
def remapBytes(x: Nat): Fin 64 :=
  if h: capitalA! ≤ x ∧ x ≤ capitalZ! then
    ⟨ x - capitalA! + 27, (by omega) ⟩
  else if h: lowerA! ≤ x ∧ x ≤ lowerZ! then
    ⟨ x - lowerA! + 1, (by omega) ⟩
  else
    0

-- Returns a 64-bit number with the x-th bit set
def toBitSet(x: Fin 64): UInt64 :=
  let y := UInt64.ofFin (x.castLE (by decide))
  1 <<< y

def containedChars(compartment: String.Slice): UInt64 :=
  (compartment.bytes.map (fun x => x.toNat |> remapBytes |> toBitSet)).fold (fun x y => x ||| y) 0

def findCommon [Std.Iterators.Iterator α Id String.Slice] (lines: Std.Iter (α := α) (String.Slice)): Nat :=
  ((lines.map containedChars).fold (fun x y => x &&& y) u64Max).log2.toNat

def findCommonInCompartments(line: String.Slice): Nat :=
  let mid := line.utf8ByteSize / 2
  findCommon [line.take mid, line.drop mid].iter

def part1Solution(input: String): Nat :=
  ((input.trimAscii.split "\n").map findCommonInCompartments).fold Nat.add 0

def part2Solution(input: String): Nat :=
  let lines := (input.trimAscii.split "\n").toList
  foldChunks lines 0
  where foldChunks(xs: List String.Slice) (acc: Nat): Nat :=
  match xs with
  | _ :: _ :: [] | _ :: [] | []  => acc
  | a :: b :: c :: tail => foldChunks tail (acc + findCommon [a, b, c].iter)

-- Theorems showing the bytes are mapped correctly
theorem remap_caps(x: Nat) (h: capitalA! ≤ x ∧ x ≤ capitalZ!): 27 ≤ remapBytes x ∧ remapBytes x ≤ 52 := by
  simp [remapBytes, h]
  grind

theorem remap_caps_seq(x: Nat) (h: capitalA! ≤ x ∧ x < capitalZ!): remapBytes (x + 1) = 1 + remapBytes x := by
  simp [remapBytes, h]
  grind

theorem remap_lowercase(x: Nat) (h: lowerA! ≤ x ∧ x ≤ lowerZ!): 1 ≤ remapBytes x ∧ remapBytes x ≤ 26 := by
  simp [remapBytes, h]
  grind

theorem remap_lowercase_seq(x: Nat) (h: lowerA! ≤ x ∧ x < lowerZ!): remapBytes (x + 1) = 1 + remapBytes x := by
  simp [remapBytes, h]
  grind
