import AdventOfCode.Common.Fin
import AdventOfCode.Common.Result
import Std.Data.HashMap

-- Label the numbers to make sure values in the list
-- are unique.
structure LabelledInt where
  label: Nat
  value: Int
deriving BEq, Hashable

instance: EquivBEq LabelledInt where
  rfl := by simp [BEq.beq, instBEqLabelledInt.beq]
  symm := by simp [BEq.beq, instBEqLabelledInt.beq]; grind
  trans := by simp [BEq.beq, instBEqLabelledInt.beq]; grind

instance: LawfulHashable LabelledInt where
  hash_eq := by
    simp [Hashable.hash, instHashableLabelledInt.hash, BEq.beq, instBEqLabelledInt.beq]
    grind

instance: ToString LabelledInt where
  toString x := s!"{x.value}"

-- Special Map type where the keys are known to come from
-- some original vector.
def IndexMap (original : Vector LabelledInt n): Type :=
  { m : Std.HashMap LabelledInt (Fin n) // ∀ i : Fin n, (original.get i) ∈ m }

-- A version of `IndexMap` where the keys only comes from part of
-- the original vector. This type is used in building up to `IndexMap`
-- in a loop.
def PartialIndexMap (original : Vector LabelledInt n) (k: Nat): Type :=
  { m : Std.HashMap LabelledInt (Fin n) // ∀ i : Fin n, i.val < k → (original.get i) ∈ m }

def PartialIndexMap.cast (m: PartialIndexMap original k) (k_eq_n: k = n): PartialIndexMap original n :=
  ⟨m.val, fun i h => m.property i (by omega)⟩

-- Recursive function that builds up a `PartialIndexMap` based on all
-- indices in `original` (`k = n`)
def makeIndexMapAux (original : Vector LabelledInt n) (k: Nat) (h1: k ≤ n) (m: PartialIndexMap original k): PartialIndexMap original n :=
  if h2: k = n then m.cast h2
  else
    have h3: k < n := by omega
    makeIndexMapAux original (k + 1) (by omega) (insertElemK original k h3 m)
  where insertElemK
    (original : Vector LabelledInt n)
    (k: Nat)
    (h: k < n)
    (m: PartialIndexMap original k): PartialIndexMap original (k + 1)
  :=
    let i: Fin n := ⟨k, h⟩
    let m' := m.val.insert (original.get i) i
    have h1: (original.get i) ∈ m' := by grind
    ⟨m', fun j h1 => by grind⟩

-- Construct an `IndexMap`
def makeIndexMap (original : Vector LabelledInt n): IndexMap original :=
  let base: PartialIndexMap original 0 := ⟨∅, by grind⟩
  let ⟨m, hm⟩ := makeIndexMapAux original 0 (by omega) base
  ⟨m, fun i => hm i i.isLt⟩

-- State that is modified during the "mixing" process
structure State (n: Nat) where
  original: Vector LabelledInt n
  current: Vector LabelledInt n
  indexMap: Std.HashMap LabelledInt (Fin n)

-- Helper type that holds on to proofs of elements
-- existing in the state.
def InclusionFn (orig state: State n): Prop :=
  (x: LabelledInt) → (x ∈ orig.original) → (x ∈ state.indexMap)

structure StateWithInclusionProof (orig: State n) where
  state: State n
  inclusion: InclusionFn orig state

def State.create (original: Vector LabelledInt n): (orig: State n) × (StateWithInclusionProof orig) :=
  let current := original
  let ⟨indexMap, indexInclusion⟩ := makeIndexMap original
  let orig: State n := ⟨original, current, indexMap⟩
  let inclusion: InclusionFn orig orig := (
    fun x h => by
      have h1: ∃ (i: Nat) (h: i < n), orig.original.get ⟨i, h⟩ = x := by
        rw [Vector.mem_iff_getElem] at h
        exact h
      cases h1 with
      | intro i h1 => cases h1 with
      | intro h h1 =>
        let i: Fin n := ⟨i, h⟩
        rw [← h1]
        apply indexInclusion
  )
  ⟨orig, ⟨orig, inclusion⟩⟩

-- Compute the index to move the element `x` to
-- based on the rules of the puzzle.
def computeNewIndex (currentIndex: Fin n) (h: 1 < n) (x: LabelledInt): Fin n :=
  let a: Int := x.value + (Int.ofNat currentIndex.val)
  let b: Int := Int.ofNat (n - 1)
  let i := a % b
  have b_ne_zero : b ≠ 0 := by grind
  have i_range: 0 ≤ i ∧ i < b := by
    have h: a % b = i := by trivial
    rw [Int.emod_eq_iff b_ne_zero] at h
    grind
  ⟨i.natAbs, by grind⟩

-- Helper function for the fold used in `shiftLeft`
def shiftLeftAux
  (n k: Nat)
  (currentIndex: Nat)
  (h: k + currentIndex < n)
  (input: (Vector LabelledInt n) × (Std.HashMap LabelledInt (Fin n)))
  (i: Fin k): (Vector LabelledInt n) × (Std.HashMap LabelledInt (Fin n))
:=
  let ⟨accVec, accMap⟩ := input
  let a: Fin (n - 1) := (i.addNat currentIndex).castLT (by omega)
  let b := a.succ.cast (by omega)
  let y := accVec.get b
  (accVec.set a y, accMap.insert y (a.castLT (by omega)))

-- Move the element at `currentIndex` to `destIndex`, where `destIndex` is further
-- in the list, thus causing all the elements in between `currentIndex` and `destIndex`
-- to shift to the left.
def shiftLeft (state: State n) (currentIndex destIndex: Fin n) (h: currentIndex < destIndex): State n :=
  let x := state.current.get currentIndex
  let k := destIndex.val - currentIndex.val
  let ⟨current, indexMap⟩ := Fin.foldl k
    (shiftLeftAux n k currentIndex.val (by omega))
    (state.current, state.indexMap)
  ⟨state.original, current.set destIndex x, indexMap.insert x destIndex⟩

-- Theorems showing that the shifting operation
-- does not impact membership in the `indexMap`
theorem shift_left_aux_retains_elements
  (n k: Nat)
  (currentIndex: Fin n)
  (h1: k + currentIndex < n)
  (input: (Vector LabelledInt n) × (Std.HashMap LabelledInt (Fin n)))
  (i: Fin k)
  (y: LabelledInt)
  (h2: y ∈ input.snd): y ∈ (shiftLeftAux n k currentIndex h1 input i).snd
:= by
  simp [shiftLeftAux]
  grind

theorem shift_left_retains_elements
  (state: State n)
  (currentIndex destIndex: Fin n)
  (h1: currentIndex < destIndex)
  (y: LabelledInt)
  (h2: y ∈ state.indexMap): y ∈ (shiftLeft state currentIndex destIndex h1).indexMap
:= by
  simp [shiftLeft]
  let k := destIndex.val - currentIndex.val
  let LoopType: Type := (Vector LabelledInt n) × (Std.HashMap LabelledInt (Fin n))
  let p: LoopType → Prop := fun s => y ∈ s.snd
  let f: LoopType → Fin k → LoopType := (shiftLeftAux n k currentIndex (by omega))
  let loop_inv: (lt: LoopType) → (i: Fin k) → (p lt) → p (f lt i) := (
    fun lt i h1 => shift_left_aux_retains_elements n k currentIndex (by omega) lt i y h1
  )
  have conclusion: p (Fin.foldl k f (state.current, state.indexMap)) := loop_invariant p k (state.current, state.indexMap) h2 f loop_inv
  grind

-- Helper function for the fold used in `shiftRight`
def shiftRightAux
  (n k: Nat)
  (currentIndex: Fin n)
  (input: (Vector LabelledInt n) × (Std.HashMap LabelledInt (Fin n)))
  (i: Fin k): (Vector LabelledInt n) × (Std.HashMap LabelledInt (Fin n))
:=
  let ⟨accVec, accMap⟩ := input
  let a: Nat := currentIndex.val - i.val
  let b: Fin n := ⟨a - 1, by omega⟩
  let y := accVec.get b
  (accVec.set a y, accMap.insert y ⟨a, by omega⟩)

-- Move the element at `currentIndex` to `destIndex`, where `destIndex` is earlier
-- in the list, thus causing all the elements in between `currentIndex` and `destIndex`
-- to shift to the right.
def shiftRight (state: State n) (currentIndex destIndex: Fin n): State n :=
  let x := state.current.get currentIndex
  let k := currentIndex.val - destIndex.val
  let ⟨current, indexMap⟩ := Fin.foldl k
    (shiftRightAux n k currentIndex)
    (state.current, state.indexMap)
  ⟨state.original, current.set destIndex x, indexMap.insert x destIndex⟩

-- Theorems showing that the shifting operation
-- does not impact membership in the `indexMap`
theorem shift_right_aux_retains_elements
  (n k: Nat)
  (currentIndex: Fin n)
  (input: (Vector LabelledInt n) × (Std.HashMap LabelledInt (Fin n)))
  (i: Fin k)
  (y: LabelledInt)
  (h: y ∈ input.snd): y ∈ (shiftRightAux n k currentIndex input i).snd
:= by
  simp [shiftRightAux]
  grind

theorem shift_right_retains_elements
  (state: State n)
  (currentIndex destIndex: Fin n)
  (y: LabelledInt)
  (h: y ∈ state.indexMap): y ∈ (shiftRight state currentIndex destIndex).indexMap
:= by
  simp [shiftRight]
  let k := currentIndex.val - destIndex.val
  let LoopType: Type := (Vector LabelledInt n) × (Std.HashMap LabelledInt (Fin n))
  let p: LoopType → Prop := fun s => y ∈ s.snd
  let f: LoopType → Fin k → LoopType := (shiftRightAux n k currentIndex)
  let loop_inv: (lt: LoopType) → (i: Fin k) → (p lt) → p (f lt i) := (
    fun lt i h1 => shift_right_aux_retains_elements n k currentIndex lt i y h1
  )
  have conclusion: p (Fin.foldl k f (state.current, state.indexMap)) := loop_invariant p k (state.current, state.indexMap) h f loop_inv
  grind

-- Move the element `x` in the state according to the rules
-- of the puzzle (using the shifting operations above)
-- Note the `h2` membership hypothesis is needed to guarantee
-- we can look up `x` in the state in the first place, and it
-- is fulfilling this hypothesis that requires all the extra
-- theorems about element inclusion.
def move (state: State n) (h1: 1 < n) (x: LabelledInt) (h2: x ∈ state.indexMap): State n :=
  let currentIndex := state.indexMap.get x h2
  let destIndex := computeNewIndex currentIndex h1 x
  if h1: currentIndex < destIndex then
    shiftLeft state currentIndex destIndex h1
  else if currentIndex = destIndex then state
  else
    shiftRight state currentIndex destIndex

-- Theorem showing that the shifting operation
-- does not impact membership in the `indexMap`
theorem move_retains_elements
  (state: State n)
  (h1: 1 < n)
  (x: LabelledInt)
  (h2: x ∈ state.indexMap)
  (y: LabelledInt)
  (h3: y ∈ state.indexMap): y ∈ (move state h1 x h2).indexMap
:= by
  simp [move]
  if h4: state.indexMap[x] < computeNewIndex state.indexMap[x] h1 x then
    simp [h4]
    exact shift_left_retains_elements state state.indexMap[x] (computeNewIndex state.indexMap[x] h1 x) h4 y h3
  else if h5: state.indexMap[x] = computeNewIndex state.indexMap[x] h1 x then
    grind
  else
    simp [h4, h5]
    exact shift_right_retains_elements state state.indexMap[x] (computeNewIndex state.indexMap[x] h1 x) y h3

-- Perform one "mixing" operation.
def doMix
  (orig: State n)
  (h1: 1 < n)
  (state: StateWithInclusionProof orig): StateWithInclusionProof orig
:=
  Fin.foldl n (
    fun state i =>
      let x := orig.original[i]
      have orig_x: x ∈ orig.original := by grind
      have index_x: x ∈ state.state.indexMap := state.inclusion x orig_x
      let out := move state.state h1 x index_x
      let out_inclusion: InclusionFn orig out := (
        fun z orig_z => move_retains_elements state.state h1 x index_x z (state.inclusion z orig_z)
      )
      ⟨out, out_inclusion⟩
  ) state

-- Get the value the puzzle wants from the mixed vector.
def extractAnswer (xs: Vector LabelledInt n) (h: n ≠ 0): Int :=
  let zero := (xs.findFinIdx? (fun x => x.value = 0)).getD ⟨0, by omega⟩
  let a := xs.get (finMod (zero.val + 1000) n h)
  let b := xs.get (finMod (zero.val + 2000) n h)
  let c := xs.get (finMod (zero.val + 3000) n h)
  a.value + b.value + c.value

-- Part 1
def simpleMixing (xs: Array Int): Int :=
  let n := xs.size
  let original: Vector LabelledInt n := xs.toVector.zipIdx.map (
    fun ⟨value, label⟩ => { value := value, label := label}
  )
  if h: n ≤ 1 then 0
  else
    let ⟨orig, stateWithProof⟩ := State.create original
    let state := doMix orig (by omega) stateWithProof
    extractAnswer state.state.current (by omega)

-- Part 2
def properMixing (xs: Array Int): Int :=
  let n := xs.size
  let original: Vector LabelledInt n := xs.toVector.zipIdx.map (
    fun ⟨value, label⟩ => { value := 811589153 * value, label := label}
  )
  if h: n ≤ 1 then 0
  else
    let ⟨orig, stateWithProof⟩ := State.create original
    let state := Fin.foldl 10 (
      fun s _ => doMix orig (by omega) s
    ) stateWithProof
    extractAnswer state.state.current (by omega)

def part1Solution (input: String): Result Int :=
  let xs: Option (Array Int) := ((input.trimAscii.split "\n").mapM String.Slice.toInt?).toArray
  (getOrErr xs "Failed to parse Int").map simpleMixing

def part2Solution (input: String): Result Int :=
  let xs: Option (Array Int) := ((input.trimAscii.split "\n").mapM String.Slice.toInt?).toArray
  (getOrErr xs "Failed to parse Int").map properMixing
