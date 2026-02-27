import AdventOfCode.Common.Result

inductive Packet where
  | list (xs: List Packet): Packet
  | value (x: Nat): Packet

def Packet.mkString (p: Packet): String :=
  match p with
  | Packet.value x => s!"{x}"
  | Packet.list xs => (xs.map Packet.mkString).toString
termination_by sizeOf p

instance: ToString Packet where
  toString := Packet.mkString

inductive Order where
  | LT: Order
  | EQ: Order
  | GT: Order
deriving Nonempty

def Order.isLT (x: Order): Bool :=
  match x with
  | Order.LT => true
  | Order.EQ | Order.GT => false

def Order.isEQ (x: Order): Bool :=
  match x with
  | Order.EQ => true
  | Order.LT | Order.GT => false

def Order.ofNats (x y: Nat): Order :=
  if x = y then Order.EQ
  else if x < y then Order.LT
  else Order.GT

def compare (a b: Packet): Order :=
  match a with
  | Packet.value x => match b with
    | Packet.value y => Order.ofNats x y
    | Packet.list ys => match ys with
      | [] => Order.GT
      | yHead :: ysTail => match compare (Packet.value x) yHead with
        | Order.EQ => if ysTail.isEmpty then Order.EQ else Order.LT
        | other => other
  | Packet.list xs => match b with
    | Packet.value y => match xs with
      | [] => Order.LT
      | xHead :: xsTail => match compare xHead (Packet.value y) with
        | Order.EQ => if xsTail.isEmpty then Order.EQ else Order.GT
        | other => other
    | Packet.list ys => match xs with
      | [] => match ys with
        | [] => Order.EQ
        | _ => Order.LT
      | xHead :: xsTail => match ys with
        | [] => Order.GT
        | yHead :: ysTail => match compare xHead yHead with
          | Order.EQ => compare (Packet.list xsTail) (Packet.list ysTail)
          | other => other

structure ParserState (s: String.Slice) where
  arr: Array String.Slice
  segStart: s.Pos
  depth: Nat

def ParserState.begin (s: String.Slice): ParserState s :=
  ⟨#[], s.startPos, 0⟩

def ParserState.update {s: String.Slice} (state: ParserState s) (p: {p: s.Pos // p ≠ s.endPos}): Result (ParserState s) :=
  let ⟨p, h⟩ := p
  match p.get h with
  | '[' => Except.ok ⟨state.arr, state.segStart, state.depth + 1⟩
  | ']' =>
    if state.depth = 0 then Except.error "Unexpected close bracket"
    else Except.ok ⟨state.arr, state.segStart, state.depth - 1⟩
  | ',' =>
    if state.depth = 0 then
      if h2: state.segStart ≤ p then
        let subslice := s.slice state.segStart p h2
        Except.ok ⟨state.arr.push subslice, p.next h, state.depth⟩
      else Except.error "TODO: unreachable; should be able to prove h2"
    else
      Except.ok ⟨state.arr, state.segStart, state.depth⟩
  | _ => Except.ok ⟨state.arr, state.segStart, state.depth⟩


def splitList (input: String.Slice): Result (List String.Slice) := do
  let state ← input.positions.foldM ParserState.update (ParserState.begin input)
  if state.depth ≠ 0 then Except.error "Mismatch brackets"
  else
    let finalSlice := input.sliceFrom state.segStart
    pure (state.arr.push finalSlice).toList

-- TODO: termination proof
partial def parsePacket (input: String.Slice): Result Packet :=
  if input.isEmpty then Except.error "Empty slice"
  else if input == "[]" then Except.ok (Packet.list [])
  else match input.toNat? with
  | some x => Except.ok (Packet.value x)
  | none =>
    if input.startsWith "[" ∧ input.endsWith "]" then
      let innerSlice := input.sliceFrom input.startPos.next!
      let innerSlice := innerSlice.sliceTo innerSlice.endPos.prev!
      do
        let slices ← splitList innerSlice
        let packets ← slices.mapM parsePacket
        pure (Packet.list packets)
    else Except.error s!"Unknown packet format {input}"

def parsePacketPair (input: String.Slice): Result (Packet × Packet) :=
  match (input.split "\n").toList with
  | a :: b :: [] => do
    let x ← parsePacket a
    let y ← parsePacket b
    pure (x, y)
  | _ => Except.error "Failed to parse packet pair"

def part1Solution(input: String): Result Nat := do
  let pairs := (input.trimAscii.split "\n\n").mapM parsePacketPair
  let ⟨acc, _⟩ ← pairs.fold (fun ⟨acc, i⟩ ⟨a, b⟩ => if (compare a b).isLT then (acc + i, i + 1) else (acc, i + 1)) (0, 1)
  pure acc

def part2Solution(input: String): Result Nat := do
  let lines := (input.trimAscii.split "\n").filter (fun s => ¬s.isEmpty)
  let packets ← (lines.mapM parsePacket).toArray
  let sep1 ← parsePacket "[[2]]"
  let sep2 ← parsePacket "[[6]]"
  let packets := packets.push sep1
  let packets := packets.push sep2
  let sorted := packets.insertionSort (fun p q => (compare p q).isLT)
  let ⟨a, b, _⟩ := sorted.foldl (
    fun ⟨a, b, i⟩ packet =>
      if (compare packet sep1).isEQ then (i, b, i + 1)
      else if (compare packet sep2).isEQ then (a, i, i + 1)
      else (a, b, i + 1)
  ) (0, 0, 1)
  pure (a * b)

-- Theorems about the compare function
-- TODO: is there a more concise way to do these proofs?

-- Reflexive
theorem compare_eq (p: Packet): compare p p = Order.EQ := by
  cases p with
  | value x => simp [_root_.compare, Order.ofNats]
  | list xs => cases xs with
    | nil => simp [_root_.compare]
    | cons xHead xsTail =>
      simp [_root_.compare, compare_eq xHead, compare_eq (Packet.list xsTail)]

theorem order_of_nats_eq (x: Nat): Order.ofNats x x = Order.EQ := by
  simp [Order.ofNats]

theorem order_of_nats_anti_sym (x y: Nat) (h: Order.ofNats x y = Order.LT): Order.ofNats y x = Order.GT := by
  simp [Order.ofNats] at h ⊢
  grind

theorem order_of_nats_trans (x y z: Nat) (h1: Order.ofNats x y = Order.LT) (h2: Order.ofNats y z = Order.LT): Order.ofNats x z = Order.LT := by
  simp [Order.ofNats] at *
  have h3: x < y := by grind
  have h4: y < z := by grind
  have h5: x < z := by omega
  simp [h5]
  omega

-- Helper theorem for doing cases on possible values of an Order-typed expression
theorem order_exhaustive (x: Order) (h1: x ≠ Order.LT) (h2: x ≠ Order.GT): x = Order.EQ := by
  cases x <;> grind

-- Symmetric in the equality case
theorem compare_symm (p q: Packet) (h: compare p q = Order.EQ): compare q p = Order.EQ := by
  cases p with
  | value x => cases q with
    | value y =>
      simp [_root_.compare, Order.ofNats] at h ⊢
      grind
    | list ys => cases ys with
      | nil => simp [_root_.compare] at h
      | cons yHead ysTail =>
        simp [_root_.compare] at h ⊢
        if h2: compare (Packet.value x) yHead = Order.LT then
          simp [h2] at h
        else if h3: compare (Packet.value x) yHead = Order.GT then
          simp [h3] at h
        else
          have h4: compare (Packet.value x) yHead = Order.EQ := order_exhaustive (compare (Packet.value x) yHead) h2 h3
          simp [h4] at h
          simp [compare_symm (Packet.value x) yHead h4]
          exact h
  | list xs => cases xs with
    | nil => cases q with
      | value y => simp [_root_.compare] at h
      | list ys => cases ys with
        | nil => exact compare_eq (Packet.list [])
        | cons yHead ysTail => simp [_root_.compare] at h
    | cons xHead xsTail => cases q with
      | value y =>
        simp [_root_.compare] at h ⊢
        if h2: compare xHead (Packet.value y) = Order.LT then simp [h2] at h
        else if h3: compare xHead (Packet.value y) = Order.GT then simp [h3] at h
        else
          have h4: compare xHead (Packet.value y) = Order.EQ := order_exhaustive (compare xHead (Packet.value y)) h2 h3
          simp [h4] at h
          simp [compare_symm xHead (Packet.value y) h4]
          exact h
      | list ys => cases ys with
        | nil => simp [_root_.compare] at h
        | cons yHead ysTail =>
          simp [_root_.compare] at h ⊢
          if h2: compare xHead yHead = Order.LT then simp [h2] at h
          else if h3: compare xHead yHead = Order.GT then simp [h3] at h
          else
            have h4: compare xHead yHead = Order.EQ := order_exhaustive (compare xHead yHead) h2 h3
            simp [h4] at h
            simp [compare_symm xHead yHead h4]
            exact compare_symm (Packet.list xsTail) (Packet.list ysTail) h
termination_by (sizeOf p) + (sizeOf q)

-- Anti-symmetric in the non-equal case
theorem compare_anti_sym (p q: Packet) (h: compare p q = Order.LT): compare q p = Order.GT := by
  cases p with
  | value x => cases q with
    | value y =>
      simp [_root_.compare] at h ⊢
      exact order_of_nats_anti_sym x y h
    | list ys => cases ys with
      | nil => simp [_root_.compare] at h ⊢
      | cons yHead ysTail =>
        simp [_root_.compare] at h ⊢
        if h2: compare (Packet.value x) yHead = Order.LT then
          simp [compare_anti_sym (Packet.value x) yHead h2]
        else if h3: compare (Packet.value x) yHead = Order.GT then
          simp [h3] at h
        else
          have h4: compare (Packet.value x) yHead = Order.EQ := order_exhaustive (compare (Packet.value x) yHead) h2 h3
          have h5: compare yHead (Packet.value x) = Order.EQ := compare_symm (Packet.value x) yHead h4
          simp [h4] at h
          simp [h5]
          exact h
  | list xs => cases xs with
    | nil => cases q with
      | value y => simp [_root_.compare] at h ⊢
      | list ys => cases ys with
        | nil => simp [_root_.compare] at h
        | cons yHead ysTail => simp [_root_.compare] at h ⊢
    | cons xHead xsTail => cases q with
      | value y =>
        simp [_root_.compare] at h ⊢
        if h2: compare xHead (Packet.value y) = Order.LT then
          simp [compare_anti_sym xHead (Packet.value y) h2]
        else if h3: compare xHead (Packet.value y) = Order.GT then simp [h3] at h
        else
          have h4: compare xHead (Packet.value y) = Order.EQ := order_exhaustive (compare xHead (Packet.value y)) h2 h3
          simp [h4] at h
          grind
      | list ys => cases ys with
        | nil => simp [_root_.compare] at h
        | cons yHead ysTail =>
          simp [_root_.compare] at h ⊢
          if h2: compare xHead yHead = Order.LT then
            simp [compare_anti_sym xHead yHead h2]
          else if h3: compare xHead yHead = Order.GT then simp [h3] at h
          else
            have h4: compare xHead yHead = Order.EQ := order_exhaustive (compare xHead yHead) h2 h3
            have h5: compare yHead xHead = Order.EQ := compare_symm xHead yHead h4
            simp [h4] at h
            simp [h5]
            exact compare_anti_sym (Packet.list xsTail) (Packet.list ysTail) h
termination_by (sizeOf p) + (sizeOf q)

theorem compare_anti_sym2 (p q: Packet) (h: compare p q = Order.GT): compare q p = Order.LT := by
  cases p with
  | value x => cases q with
    | value y =>
      simp [_root_.compare, Order.ofNats] at h ⊢
      grind
    | list ys => cases ys with
      | nil => simp [_root_.compare] at h ⊢
      | cons yHead ysTail =>
        simp [_root_.compare] at h ⊢
        if h2: compare (Packet.value x) yHead = Order.LT then
          simp [h2] at h
        else if h3: compare (Packet.value x) yHead = Order.GT then
          simp [compare_anti_sym2 (Packet.value x) yHead h3]
        else
          have h4: compare (Packet.value x) yHead = Order.EQ := order_exhaustive (compare (Packet.value x) yHead) h2 h3
          simp [h4] at h
          grind
  | list xs => cases xs with
    | nil => cases q with
      | value y => simp [_root_.compare] at h ⊢
      | list ys => cases ys with
        | nil => simp [_root_.compare] at h
        | cons yHead ysTail => simp [_root_.compare] at h ⊢
    | cons xHead xsTail => cases q with
      | value y =>
        simp [_root_.compare] at h ⊢
        if h2: compare xHead (Packet.value y) = Order.LT then
          simp [h2] at h
        else if h3: compare xHead (Packet.value y) = Order.GT then
          simp [compare_anti_sym2 xHead (Packet.value y) h3]
        else
          have h4: compare xHead (Packet.value y) = Order.EQ := order_exhaustive (compare xHead (Packet.value y)) h2 h3
          have h5: compare (Packet.value y) xHead = Order.EQ := compare_symm xHead (Packet.value y) h4
          simp [h4] at h
          simp [h5]
          exact h
      | list ys => cases ys with
        | nil => simp [_root_.compare] at h ⊢
        | cons yHead ysTail =>
          simp [_root_.compare] at h ⊢
          if h2: compare xHead yHead = Order.LT then
            simp [h2] at h
          else if h3: compare xHead yHead = Order.GT then
            simp [compare_anti_sym2 xHead yHead h3]
          else
            have h4: compare xHead yHead = Order.EQ := order_exhaustive (compare xHead yHead) h2 h3
            have h5: compare yHead xHead = Order.EQ := compare_symm xHead yHead h4
            simp [h4] at h
            simp [h5]
            exact compare_anti_sym2 (Packet.list xsTail) (Packet.list ysTail) h
termination_by (sizeOf p) + (sizeOf q)

-- Equality is transitive
theorem compare_eq_trans (p q r: Packet) (h_p_eq_q: compare p q = Order.EQ) (h_q_eq_r: compare q r = Order.EQ): compare p r = Order.EQ := by
  cases p with
  | value x => cases q with
    | value y => cases r with
      | value z =>
        simp [_root_.compare, Order.ofNats] at *
        grind
      | list zs => cases zs with
        | nil => simp [_root_.compare] at h_q_eq_r
        | cons zHead zsTail =>
          simp [_root_.compare] at h_q_eq_r ⊢
          if h1: compare (Packet.value y) zHead = Order.LT then simp [h1] at h_q_eq_r
          else if h2: compare (Packet.value y) zHead = Order.GT then simp [h2] at h_q_eq_r
          else
            have h3: compare (Packet.value y) zHead = Order.EQ := order_exhaustive (compare (Packet.value y) zHead) h1 h2
            simp [h3] at h_q_eq_r
            simp [compare_eq_trans (Packet.value x) (Packet.value y) zHead h_p_eq_q h3]
            exact h_q_eq_r
    | list ys => cases ys with
      | nil => simp [_root_.compare] at h_p_eq_q
      | cons yHead ysTail =>
        simp [_root_.compare] at h_p_eq_q
        if h1: compare (Packet.value x) yHead = Order.LT then simp [h1] at h_p_eq_q
        else if h2: compare (Packet.value x) yHead = Order.GT then simp [h2] at h_p_eq_q
        else
          have h3: compare (Packet.value x) yHead = Order.EQ := order_exhaustive (compare (Packet.value x) yHead) h1 h2
          simp [h3] at h_p_eq_q
          simp [h_p_eq_q] at h_q_eq_r
          cases r with
          | value z =>
            simp [_root_.compare] at h_q_eq_r
            if h4: compare yHead (Packet.value z) = Order.LT then simp [h4] at h_q_eq_r
            else if h5: compare yHead (Packet.value z) = Order.GT then simp [h5] at h_q_eq_r
            else
              have h6: compare yHead (Packet.value z) = Order.EQ := order_exhaustive (compare yHead (Packet.value z)) h4 h5
              exact compare_eq_trans (Packet.value x) yHead (Packet.value z) h3 h6
          | list zs => cases zs with
            | nil => simp [_root_.compare] at h_q_eq_r
            | cons zHead zsTail =>
              simp [_root_.compare] at h_q_eq_r
              if h4: compare yHead zHead = Order.LT then simp [h4] at h_q_eq_r
              else if h5: compare yHead zHead = Order.GT then simp [h5] at h_q_eq_r
              else
                have h6: compare yHead zHead = Order.EQ := order_exhaustive (compare yHead zHead) h4 h5
                simp [h6] at h_q_eq_r
                cases zsTail with
                | nil =>
                  simp [_root_.compare]
                  simp [compare_eq_trans (Packet.value x) yHead zHead h3 h6]
                | cons _ _ => simp [_root_.compare] at h_q_eq_r
  | list xs => cases xs with
    | nil => cases q with
      | value y => simp [_root_.compare] at h_p_eq_q
      | list ys => cases ys with
        | nil => cases r with
          | value z => simp [_root_.compare] at h_q_eq_r
          | list zs => cases zs with
            | nil => simp [_root_.compare]
            | cons zHead zsTail => simp [_root_.compare] at h_q_eq_r
        | cons yHead ysTail => simp [_root_.compare] at h_p_eq_q
    | cons xHead xsTail => cases q with
      | value y => cases r with
        | value z =>
          simp [_root_.compare, Order.ofNats] at h_q_eq_r
          have h1: y = z := by grind
          rw [← h1]
          exact h_p_eq_q
        | list zs => cases zs with
          | nil => simp [_root_.compare] at h_q_eq_r
          | cons zHead zsTail =>
            simp [_root_.compare] at h_q_eq_r
            if h1: compare (Packet.value y) zHead = Order.LT then simp [h1] at h_q_eq_r
            else if h2: compare (Packet.value y) zHead = Order.GT then simp [h2] at h_q_eq_r
            else
              have h3: compare (Packet.value y) zHead = Order.EQ := order_exhaustive (compare (Packet.value y) zHead) h1 h2
              simp [_root_.compare] at h_p_eq_q ⊢
              if h4: compare xHead (Packet.value y) = Order.LT then simp [h4] at h_p_eq_q
              else if h5: compare xHead (Packet.value y) = Order.GT then simp [h5] at h_p_eq_q
              else
                have h6: compare xHead (Packet.value y) = Order.EQ := order_exhaustive (compare xHead (Packet.value y)) h4 h5
                simp [compare_eq_trans xHead (Packet.value y) zHead h6 h3]
                cases xsTail with
                | nil => cases zsTail with
                  | nil => simp [_root_.compare]
                  | cons _ _ => simp [h3] at h_q_eq_r
                | cons _ _ => simp [h6] at h_p_eq_q
      | list ys => cases ys with
        | nil => cases r with
          | value z => simp [_root_.compare] at h_q_eq_r
          | list zs => simp [_root_.compare] at h_p_eq_q
        | cons yHead ysTail => cases r with
          | value z =>
            simp [_root_.compare] at h_q_eq_r
            if h1: compare yHead (Packet.value z) = Order.LT then simp [h1] at h_q_eq_r
            else if h2: compare yHead (Packet.value z) = Order.GT then simp [h2] at h_q_eq_r
            else
              have h3: compare yHead (Packet.value z) = Order.EQ := order_exhaustive (compare yHead (Packet.value z)) h1 h2
              simp [h3] at h_q_eq_r
              simp [_root_.compare, h_q_eq_r] at h_p_eq_q
              if h4: compare xHead yHead = Order.LT then simp [h4] at h_p_eq_q
              else if h5: compare xHead yHead = Order.GT then simp [h5] at h_p_eq_q
              else
                have h6: compare xHead yHead = Order.EQ := order_exhaustive (compare xHead yHead) h4 h5
                simp [h6] at h_p_eq_q
                cases xsTail with
                | nil =>
                  simp [_root_.compare]
                  simp [compare_eq_trans xHead yHead (Packet.value z) h6 h3]
                | cons _ _ => simp [_root_.compare] at h_p_eq_q
          | list zs => cases zs with
            | nil => simp [_root_.compare] at h_q_eq_r
            | cons zHead zsTail =>
              simp [_root_.compare] at *
              if h1: compare xHead yHead = Order.LT then simp [h1] at h_p_eq_q
              else if h2: compare xHead yHead = Order.GT then simp [h2] at h_p_eq_q
              else
                have h3: compare xHead yHead = Order.EQ := order_exhaustive (compare xHead yHead) h1 h2
                simp [h3] at h_p_eq_q
                if h4: compare yHead zHead = Order.LT then simp [h4] at h_q_eq_r
                else if h5: compare yHead zHead = Order.GT then simp [h5] at h_q_eq_r
                else
                  have h6: compare yHead zHead = Order.EQ := order_exhaustive (compare yHead zHead) h4 h5
                  simp [h6] at h_q_eq_r
                  simp [compare_eq_trans xHead yHead zHead h3 h6]
                  exact compare_eq_trans (Packet.list xsTail) (Packet.list ysTail) (Packet.list zsTail) h_p_eq_q h_q_eq_r
termination_by (sizeOf p) + (sizeOf q) + (sizeOf r)

-- p < q ∧ q = r => p < r
theorem compare_eq_lt_trans (p q r: Packet) (h_p_lt_q: compare p q = Order.LT) (h_q_eq_r: compare q r = Order.EQ): compare p r = Order.LT := by
  cases p with
  | value x => cases q with
    | value y => cases r with
      | value z =>
        simp [_root_.compare, Order.ofNats] at *
        grind
      | list zs => cases zs with
        | nil => simp [_root_.compare] at h_q_eq_r
        | cons zHead zsTail =>
          simp [_root_.compare] at h_q_eq_r ⊢
          if h1: compare (Packet.value y) zHead = Order.LT then
            simp [h1] at h_q_eq_r
          else if h2: compare (Packet.value y) zHead = Order.GT then
            simp [h2] at h_q_eq_r
          else
            have h3: compare (Packet.value y) zHead = Order.EQ := order_exhaustive (compare (Packet.value y) zHead) h1 h2
            simp [h3] at h_q_eq_r
            simp [compare_eq_lt_trans (Packet.value x) (Packet.value y) zHead h_p_lt_q h3]
    | list ys => cases ys with
      | nil => simp [_root_.compare] at h_p_lt_q
      | cons yHead ysTail => cases r with
        | value z =>
          simp [_root_.compare] at h_q_eq_r
          if h1: compare yHead (Packet.value z) = Order.LT then
            simp [h1] at h_q_eq_r
          else if h2: compare yHead (Packet.value z) = Order.GT then
            simp [h2] at h_q_eq_r
          else
            have h3: compare yHead (Packet.value z) = Order.EQ := order_exhaustive (compare yHead (Packet.value z)) h1 h2
            simp [h3] at h_q_eq_r
            simp [h_q_eq_r, _root_.compare] at h_p_lt_q
            have h4: compare (Packet.value x) yHead = Order.LT := by grind
            exact compare_eq_lt_trans (Packet.value x) yHead (Packet.value z) h4 h3
        | list zs => cases zs with
          | nil => simp [_root_.compare] at h_q_eq_r
          | cons zHead zsTail =>
            simp [_root_.compare] at *
            if h1: compare yHead zHead = Order.LT then simp [h1] at h_q_eq_r
            else if h2: compare yHead zHead = Order.GT then simp [h2] at h_q_eq_r
            else
              have h3: compare yHead zHead = Order.EQ := order_exhaustive (compare yHead zHead) h1 h2
              simp [h3] at h_q_eq_r
              cases ysTail with
              | nil =>
                have h4: compare (Packet.value x) yHead = Order.LT := by grind
                simp [compare_eq_lt_trans (Packet.value x) yHead zHead h4 h3]
              | cons innerHead innerTail =>
                if h4: compare (Packet.value x) yHead = Order.LT then simp [compare_eq_lt_trans (Packet.value x) yHead zHead h4 h3]
                else if h5: compare (Packet.value x) yHead = Order.GT then simp [h5] at h_p_lt_q
                else
                  have h6: compare (Packet.value x) yHead = Order.EQ := order_exhaustive (compare (Packet.value x) yHead) h4 h5
                  have h7: compare (Packet.value x) zHead = Order.EQ := compare_eq_trans (Packet.value x) yHead zHead h6 h3
                  simp [h7]
                  cases zsTail with
                  | nil => simp [_root_.compare] at h_q_eq_r
                  | cons _ _ =>
                    simp [_root_.compare] at h_q_eq_r
                    grind
  | list xs => cases xs with
    | nil => cases q with
      | value y => cases r with
        | value z => simp [_root_.compare]
        | list zs => cases zs with
          | nil => simp [_root_.compare] at h_q_eq_r
          | cons zHead zsTail => simp [_root_.compare]
      | list ys => cases ys with
        | nil => simp [_root_.compare] at h_p_lt_q
        | cons yHead ysTail => cases r with
          | value z => simp [_root_.compare]
          | list zs => cases zs with
            | nil => simp [_root_.compare] at h_q_eq_r
            | cons zHead zsTail => simp [_root_.compare]
    | cons xHead xsTail => cases q with
      | value y => cases r with
        | value z =>
          simp [_root_.compare, Order.ofNats] at h_q_eq_r
          have h1: y = z := by grind
          rw [←h1]
          exact h_p_lt_q
        | list zs => cases zs with
          | nil => simp [_root_.compare] at h_q_eq_r
          | cons zHead zsTail =>
            simp [_root_.compare] at *
            if h1: compare xHead (Packet.value y) = Order.LT then
              if h2: compare (Packet.value y) zHead = Order.LT then simp [h2] at h_q_eq_r
              else if h3: compare (Packet.value y) zHead = Order.GT then simp [h3] at h_q_eq_r
              else
                have h4: compare (Packet.value y) zHead = Order.EQ := order_exhaustive (compare (Packet.value y) zHead) h2 h3
                simp [compare_eq_lt_trans xHead (Packet.value y) zHead h1 h4]
            else if h2: compare xHead (Packet.value y) = Order.GT then simp [h2] at h_p_lt_q
            else
              have h3: compare xHead (Packet.value y) = Order.EQ := order_exhaustive (compare xHead (Packet.value y)) h1 h2
              simp [h3] at h_p_lt_q
              grind
      | list ys => cases ys with
        | nil => simp [_root_.compare] at h_p_lt_q
        | cons yHead ysTail => cases r with
          | value z =>
            simp [_root_.compare] at *
            if h1: compare xHead yHead = Order.LT then
              if h2: compare yHead (Packet.value z) = Order.LT then simp [h2] at h_q_eq_r
              else if h3: compare yHead (Packet.value z) = Order.GT then simp [h3] at h_q_eq_r
              else
                have h4: compare yHead (Packet.value z) = Order.EQ := order_exhaustive (compare yHead (Packet.value z)) h2 h3
                simp [compare_eq_lt_trans xHead yHead (Packet.value z) h1 h4]
            else if h2: compare xHead yHead = Order.GT then simp [h2] at h_p_lt_q
            else
              have h3: compare xHead yHead = Order.EQ := order_exhaustive (compare xHead yHead) h1 h2
              simp [h3] at h_p_lt_q
              if h4: compare yHead (Packet.value z) = Order.LT then simp [h4] at h_q_eq_r
              else if h5: compare yHead (Packet.value z) = Order.GT then simp [h5] at h_q_eq_r
              else
                have h6: compare yHead (Packet.value z) = Order.EQ := order_exhaustive (compare yHead (Packet.value z)) h4 h5
                simp [h6] at h_q_eq_r
                rw [h_q_eq_r] at h_p_lt_q
                cases xsTail <;> simp [_root_.compare] at h_p_lt_q
          | list zs => cases zs with
            | nil => simp [_root_.compare] at h_q_eq_r
            | cons zHead zsTail =>
              simp [_root_.compare] at *
              if h1: compare xHead yHead = Order.LT then
                if h2: compare yHead zHead = Order.LT then simp [h2] at h_q_eq_r
                else if h3: compare yHead zHead = Order.GT then simp [h3] at h_q_eq_r
                else
                  have h4: compare yHead zHead = Order.EQ := order_exhaustive (compare yHead zHead) h2 h3
                  simp [compare_eq_lt_trans xHead yHead zHead h1 h4]
              else if h2: compare xHead yHead = Order.GT then simp [h2] at h_p_lt_q
              else
                have h3: compare xHead yHead = Order.EQ := order_exhaustive (compare xHead yHead) h1 h2
                simp [h3] at h_p_lt_q
                if h4: compare yHead zHead = Order.LT then simp [h4] at h_q_eq_r
                else if h5: compare yHead zHead = Order.GT then simp [h5] at h_q_eq_r
                else
                  have h6: compare yHead zHead = Order.EQ := order_exhaustive (compare yHead zHead) h4 h5
                  simp [h6] at h_q_eq_r
                  have h7: compare xHead zHead = Order.EQ := compare_eq_trans xHead yHead zHead h3 h6
                  simp [h7]
                  exact compare_eq_lt_trans (Packet.list xsTail) (Packet.list ysTail) (Packet.list zsTail) h_p_lt_q h_q_eq_r
termination_by (sizeOf p) + (sizeOf q) + (sizeOf r)

-- p = q ∧ q < r => p < r
-- Look at this nice proof by contradiction!
theorem compare_eq_lt_trans2 (p q r: Packet) (h_p_eq_q: compare p q = Order.EQ) (h_q_lt_r: compare q r = Order.LT): compare p r = Order.LT := by
  if h1: compare p r = Order.LT then exact h1
  else if h2: compare p r = Order.GT then
    have h3: compare r p = Order.LT := compare_anti_sym2 p r h2
    have h4: compare r q = Order.LT := compare_eq_lt_trans r p q h3 h_p_eq_q
    have h5: compare q r = Order.GT := compare_anti_sym r q h4
    grind
  else
    have h3: compare p r = Order.EQ := order_exhaustive (compare p r) h1 h2
    have h4: compare q p = Order.EQ := compare_symm p q h_p_eq_q
    have h5: compare q r = Order.EQ := compare_eq_trans q p r h4 h3
    grind

-- Inequality is transitive
theorem compare_trans (p q r: Packet) (h_p_lt_q: compare p q = Order.LT) (h_q_lt_r: compare q r = Order.LT): compare p r = Order.LT := by
  cases p with
  | value x => cases q with
    | value y => cases r with
      | value z =>
        simp [_root_.compare] at *
        exact order_of_nats_trans x y z h_p_lt_q h_q_lt_r
      | list zs => cases zs with
        | nil => simp [_root_.compare] at h_q_lt_r
        | cons zHead zsTail =>
          simp [_root_.compare] at h_q_lt_r ⊢
          if h1: compare (Packet.value y) zHead = Order.LT then
            simp [compare_trans (Packet.value x) (Packet.value y) zHead h_p_lt_q h1]
          else if h2: compare (Packet.value y) zHead = Order.GT then
            simp [h2] at h_q_lt_r
          else
            have h3: compare (Packet.value y) zHead = Order.EQ := order_exhaustive (compare (Packet.value y) zHead) h1 h2
            simp [compare_eq_lt_trans (Packet.value x) (Packet.value y) zHead h_p_lt_q h3]
    | list ys => cases ys with
      | nil => simp [_root_.compare] at h_p_lt_q
      | cons yHead ysTail => cases r with
        | value z =>
          simp [_root_.compare] at h_p_lt_q h_q_lt_r
          if h1: compare (Packet.value x) yHead = Order.LT then
            if h2: compare yHead (Packet.value z) = Order.LT then
              exact compare_trans (Packet.value x) yHead (Packet.value z) h1 h2
            else if h3: compare yHead (Packet.value z) = Order.GT then simp [h3] at h_q_lt_r
            else
              have h4: compare yHead (Packet.value z) = Order.EQ := order_exhaustive (compare yHead (Packet.value z)) h2 h3
              simp [h4] at h_q_lt_r
              grind
          else if h2: compare (Packet.value x) yHead = Order.GT then simp [h2] at h_p_lt_q
          else
            have h3: compare (Packet.value x) yHead = Order.EQ := order_exhaustive (compare (Packet.value x) yHead) h1 h2
            if h4: compare yHead (Packet.value z) = Order.LT then
              exact compare_eq_lt_trans2 (Packet.value x) yHead (Packet.value z) h3 h4
            else if h5: compare yHead (Packet.value z) = Order.GT then simp [h5] at h_q_lt_r
            else
              have h6: compare yHead (Packet.value z) = Order.EQ := order_exhaustive (compare yHead (Packet.value z)) h4 h5
              simp [h6] at h_q_lt_r
              grind
        | list zs => cases zs with
          | nil => simp [_root_.compare] at h_q_lt_r
          | cons zHead zsTail =>
            simp [_root_.compare] at h_p_lt_q h_q_lt_r
            if h1: compare (Packet.value x) yHead = Order.LT then
              if h4: compare yHead zHead = Order.LT then
                simp [_root_.compare, compare_trans (Packet.value x) yHead zHead h1 h4]
              else if h5: compare yHead zHead = Order.GT then simp [h5] at h_q_lt_r
              else
                have h6: compare yHead zHead = Order.EQ := order_exhaustive (compare yHead zHead) h4 h5
                simp [h6] at h_q_lt_r
                simp [_root_.compare]
                simp [compare_eq_lt_trans (Packet.value x) yHead zHead h1 h6]
            else if h2: compare (Packet.value x) yHead = Order.GT then simp [h2] at h_p_lt_q
            else
              have h3: compare (Packet.value x) yHead = Order.EQ := order_exhaustive (compare (Packet.value x) yHead) h1 h2
              if h4: compare yHead zHead = Order.LT then
                simp [_root_.compare, compare_eq_lt_trans2 (Packet.value x) yHead zHead h3 h4]
              else if h5: compare yHead zHead = Order.GT then simp [h5] at h_q_lt_r
              else
                have h6: compare yHead zHead = Order.EQ := order_exhaustive (compare yHead zHead) h4 h5
                simp [h6] at h_q_lt_r
                simp [_root_.compare]
                simp [compare_eq_trans (Packet.value x) yHead zHead h3 h6]
                simp [h3] at h_p_lt_q
                cases zsTail with
                | nil => cases ysTail with
                  | nil => grind
                  | cons _ _ => simp [_root_.compare] at h_q_lt_r
                | cons _ _ => grind
  | list xs => cases q with
    | value y => cases r with
      | value z =>
        cases xs with
        | nil => simp [_root_.compare]
        | cons xHead xsTail =>
          simp [_root_.compare] at h_p_lt_q ⊢
          if h1: compare xHead (Packet.value y) = Order.LT then
            if h4: compare (Packet.value y) (Packet.value z) = Order.LT then
              simp [compare_trans xHead (Packet.value y) (Packet.value z) h1 h4]
            else if h5: compare (Packet.value y) (Packet.value z) = Order.GT then simp [h5] at h_q_lt_r
            else
              have h6: compare (Packet.value y) (Packet.value z) = Order.EQ := order_exhaustive (compare (Packet.value y) (Packet.value z)) h4 h5
              simp [h6] at h_q_lt_r
          else if h2: compare xHead (Packet.value y) = Order.GT then simp [h2] at h_p_lt_q
          else
            have h3: compare xHead (Packet.value y) = Order.EQ := order_exhaustive (compare xHead (Packet.value y)) h1 h2
            simp [h3] at h_p_lt_q
            grind
      | list zs => cases zs with
        | nil => simp [_root_.compare] at h_q_lt_r
        | cons zHead zsTail =>
          simp [_root_.compare] at h_q_lt_r
          if h1: compare (Packet.value y) zHead = Order.LT then
            cases xs with
              | nil => simp [_root_.compare]
              | cons xHead xsTail =>
                simp [_root_.compare] at h_p_lt_q ⊢
                if h4: compare xHead (Packet.value y) = Order.LT then
                  simp [compare_trans xHead (Packet.value y) zHead h4 h1]
                else if h5: compare xHead (Packet.value y) = Order.GT then simp [h5] at h_p_lt_q
                else
                  have h6: compare xHead (Packet.value y) = Order.EQ := order_exhaustive (compare xHead (Packet.value y)) h4 h5
                  simp [h6] at h_p_lt_q
                  grind
          else if h2: compare (Packet.value y) zHead = Order.GT then simp [h2] at h_q_lt_r
          else
            have h3: compare (Packet.value y) zHead = Order.EQ := order_exhaustive (compare (Packet.value y) zHead) h1 h2
            cases xs with
              | nil => simp [_root_.compare]
              | cons xHead xsTail =>
                simp [_root_.compare] at h_p_lt_q ⊢
                if h4: compare xHead (Packet.value y) = Order.LT then
                  simp [compare_eq_lt_trans xHead (Packet.value y) zHead h4 h3]
                else if h5: compare xHead (Packet.value y) = Order.GT then simp [h5] at h_p_lt_q
                else
                  have h6: compare xHead (Packet.value y) = Order.EQ := order_exhaustive (compare xHead (Packet.value y)) h4 h5
                  simp [h6] at h_p_lt_q
                  grind
    | list ys => cases ys with
      | nil => cases xs with
        | nil => simp [_root_.compare] at h_p_lt_q
        | cons xHead xsTail => simp [_root_.compare] at h_p_lt_q
      | cons yHead ysTail => cases xs with
        | nil => cases r with
          | value z => simp [_root_.compare]
          | list zs => cases zs with
            | nil => simp [_root_.compare] at h_q_lt_r
            | cons zHead zsTail => simp [_root_.compare]
        | cons xHead xsTail => cases r with
          | value z =>
            simp [_root_.compare] at *
            if h1: compare xHead yHead = Order.LT then
              if h4: compare yHead (Packet.value z) = Order.LT then
                simp [compare_trans xHead yHead (Packet.value z) h1 h4]
              else if h5: compare yHead (Packet.value z) = Order.GT then simp [h5] at h_q_lt_r
              else
                have h6: compare yHead (Packet.value z) = Order.EQ := order_exhaustive (compare yHead (Packet.value z)) h4 h5
                simp [compare_eq_lt_trans xHead yHead (Packet.value z) h1 h6]
            else if h2: compare xHead yHead = Order.GT then simp [h2] at h_p_lt_q
            else
              have h3: compare xHead yHead = Order.EQ := order_exhaustive (compare xHead yHead) h1 h2
              if h4: compare yHead (Packet.value z) = Order.LT then
                simp [compare_eq_lt_trans2 xHead yHead (Packet.value z) h3 h4]
              else if h5: compare yHead (Packet.value z) = Order.GT then simp [h5] at h_q_lt_r
              else
                have h6: compare yHead (Packet.value z) = Order.EQ := order_exhaustive (compare yHead (Packet.value z)) h4 h5
                simp [compare_eq_trans xHead yHead (Packet.value z) h3 h6]
                grind
          | list zs => cases zs with
            | nil => simp [_root_.compare] at h_q_lt_r
            | cons zHead zsTail =>
            simp [_root_.compare] at *
            if h1: compare xHead yHead = Order.LT then
              if h4: compare yHead zHead = Order.LT then
                simp [compare_trans xHead yHead zHead h1 h4]
              else if h5: compare yHead zHead = Order.GT then simp [h5] at h_q_lt_r
              else
                have h6: compare yHead zHead = Order.EQ := order_exhaustive (compare yHead zHead) h4 h5
                simp [compare_eq_lt_trans xHead yHead zHead h1 h6]
            else if h2: compare xHead yHead = Order.GT then simp [h2] at h_p_lt_q
            else
              have h3: compare xHead yHead = Order.EQ := order_exhaustive (compare xHead yHead) h1 h2
              if h4: compare yHead zHead = Order.LT then
                simp [compare_eq_lt_trans2 xHead yHead zHead h3 h4]
              else if h5: compare yHead zHead = Order.GT then simp [h5] at h_q_lt_r
              else
                have h6: compare yHead zHead = Order.EQ := order_exhaustive (compare yHead zHead) h4 h5
                simp [compare_eq_trans xHead yHead zHead h3 h6]
                simp [h3] at h_p_lt_q
                simp [h6] at h_q_lt_r
                exact compare_trans (Packet.list xsTail) (Packet.list ysTail) (Packet.list zsTail) h_p_lt_q h_q_lt_r
termination_by (sizeOf p) + (sizeOf q) + (sizeOf r)
