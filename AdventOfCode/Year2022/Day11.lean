import AdventOfCode.Common.Result

inductive Operation where
  | Add (n: Nat): Operation
  | Mul (n: Nat): Operation
  | Sqr: Operation

structure ThrowTo (n: Nat) where
  divisibilityCheck: Nat
  ifTrue: Fin n
  ifFalse: Fin n

structure Monkey (n: Nat) where
  items: Std.Queue Nat
  nItems: Nat
  operation: Operation
  test: ThrowTo n
  inspectCount: Nat

def Monkeys (n: Nat): Type := Vector (Monkey n) n

def Monkeys.fromArray (arr: Array (Monkey n)): Result (Monkeys n) :=
  if h: arr.size = n then Except.ok ⟨arr, h⟩
  else Except.error "Wrong size"

def ThrowTo.castDown (m: Nat) (t: ThrowTo n): Result (ThrowTo m) :=
  if h: t.ifTrue.val < m ∧ t.ifFalse.val < m then
    Except.ok ⟨t.divisibilityCheck, ⟨t.ifTrue.val, by omega⟩, ⟨t.ifFalse.val, by omega⟩⟩
  else Except.error "Monkey index too large"

def Monkey.castDown (m: Nat) (monkey: Monkey n): Result (Monkey m) := do
  let t ← monkey.test.castDown m
  pure ⟨monkey.items, monkey.nItems, monkey.operation, t, monkey.inspectCount⟩

def Operation.apply (op: Operation) (n: Nat): Nat :=
  match op with
  | Operation.Add m => n + m
  | Operation.Mul m => n * m
  | Operation.Sqr => n * n

def ThrowTo.apply (test: ThrowTo m) (n: Nat): Fin m :=
  if n % test.divisibilityCheck == 0 then test.ifTrue else test.ifFalse

def throwItem (monkey: Monkey n) (item: Nat): Monkey n :=
  let queue := monkey.items.enqueue item
  ⟨queue, monkey.nItems + 1, monkey.operation, monkey.test, monkey.inspectCount⟩

def simulateTurn (worryMod: Nat → Nat) (monkeys: Monkeys n) (activeIndex: Fin n): Monkeys n :=
  let monkey := monkeys.get activeIndex
  simHelper worryMod monkey.nItems monkey monkeys activeIndex
  where
  simHelper (worryMod: Nat → Nat) (nItems: Nat) (monkey: Monkey n) (monkeys: Monkeys n) (activeIndex: Fin n): Monkeys n :=
    if nItems = 0 then
      monkeys
    else
      match monkey.items.dequeue? with
      | some ⟨item, queue⟩ =>
        let worry := worryMod (monkey.operation.apply item)
        let targetIndex := monkey.test.apply worry
        let target := monkeys.get targetIndex
        let updated := monkeys.set targetIndex (throwItem target worry)
        let newMonkey := ⟨queue, monkey.nItems - 1, monkey.operation, monkey.test, monkey.inspectCount + 1⟩
        let finished := updated.set activeIndex newMonkey
        simHelper worryMod (nItems - 1) newMonkey finished activeIndex
      | none => monkeys -- TODO: this case is unreachable (prove it)

def simulateRound (worryMod: Nat → Nat) (monkeys: Monkeys n): Monkeys n :=
  Fin.foldl n (simulateTurn worryMod) monkeys

def parseItems (input: String.Slice): Result (Nat × Std.Queue Nat) :=
  let ns := (input.split ", ").mapM (fun x => getOrErr x.toNat? "Failed to parse number it items list")
  ns.fold (fun ⟨c, q⟩ n => (c + 1, q.enqueue n)) (0, Std.Queue.empty)

def parseOperation (input: String.Slice): Result Operation :=
  if input == "new = old * old" then
    Except.ok Operation.Sqr
  else if input.startsWith "new = old +" then
    match (input.split " ").toList with
    | _ :: _ :: _ :: _ :: n :: [] => do
      let n ← getOrErr n.toNat? "Failed to parse number in add op"
      pure (Operation.Add n)
    | _ => Except.error "Failed to parse add op"
  else if input.startsWith "new = old *" then
    match (input.split " ").toList with
    | _ :: _ :: _ :: _ :: n :: [] => do
      let n ← getOrErr n.toNat? "Failed to parse number in mul op"
      pure (Operation.Mul n)
    | _ => Except.error "Failed to parse mul op"
  else
    Except.error "Failed to parse operation"

def parseFin (m: Nat) (input: String.Slice) (msg: String): Result (Fin m) :=
  (getOrErr input.toNat? msg).bind (
    fun n =>
      if h: n < m then Except.ok ⟨n, h⟩
      else Except.error s!"{msg}: Number too large"
  )

def parseTest (m: Nat) (l1 l2 l3: String.Slice): Result (ThrowTo m) :=
  let d := match (l1.split " ").toList with
    | _ :: _ :: _ :: n :: [] => getOrErr n.toNat? "Failed to parse divisibility number"
    | _ => Except.error "Failed to parse divisibility check line"
  let t := match (l2.split " ").toList with
    | _ :: _ :: _ :: _ :: _ :: n :: [] => parseFin m n "Failed to parse true monkey index"
    | _ => Except.error "Failed to parse if true line"
  let f := match (l3.split " ").toList with
    | _ :: _ :: _ :: _ :: _ :: n :: [] => parseFin m n "Failed to parse false monkey index"
    | _ => Except.error "Failed to parse if false line"
  do
    let d ← d
    let t ← t
    let f ← f
    pure ⟨d, t, f⟩

def stripPrefix (input: String.Slice): Result String.Slice :=
  match (input.split ":").toList with
  | _ :: rest :: [] => Except.ok rest.trimAscii
  | _ => Except.error "Failed to strip line prefix"

def parseMonkey (input: String.Slice): Result (Monkey 100) :=
  match (input.split "\n").toList with
  | _ :: items :: operation :: t1 :: t2 :: t3 :: [] => do
    let ⟨nItems, i⟩ ← (stripPrefix items).bind parseItems
    let o ← (stripPrefix operation).bind parseOperation
    let t ← parseTest 100 t1.trimAscii t2.trimAscii t3.trimAscii
    pure ⟨i, nItems, o, t, 0⟩
  | _ => Except.error "Failed to parse monkey block"

def parseInput (input: String): Result ((n: Nat) × Monkeys n) := do
  let monkeys ← ((input.trimAscii.split "\n\n").mapM parseMonkey).toArray
  let n := monkeys.size
  let mapped ← monkeys.mapM (Monkey.castDown n)
  let monkeys ← Monkeys.fromArray mapped
  pure ⟨n, monkeys⟩

def topTwo (ab: Nat × Nat) (m: Monkey n): Nat × Nat :=
  let ⟨a, b⟩ := ab
  let c := m.inspectCount
  if a ≤ c then (c, a)
  else if b ≤ c then (a, c)
  else (a, b)

def part1Solution(input: String): Result Nat := do
  let ⟨_, monkeys⟩ ← parseInput input
  let worryMod := fun n => n / 3
  let endState := Fin.foldl 20 (fun ms _ => (simulateRound worryMod) ms) monkeys
  let ⟨a, b⟩ := endState.foldl topTwo (0, 0)
  pure (a * b)

def part2Solution(input: String): Result Nat := do
  let ⟨_, monkeys⟩ ← parseInput input
  let modulus := monkeys.foldl (fun n m => n * m.test.divisibilityCheck) 1
  let worryMod := fun n => n % modulus
  let endState := Fin.foldl 10000 (fun ms _ => (simulateRound worryMod) ms) monkeys
  let ⟨a, b⟩ := endState.foldl topTwo (0, 0)
  pure (a * b)
