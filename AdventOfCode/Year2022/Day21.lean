import AdventOfCode.Common.Result
import Std.Data.DHashMap

-- Can't use `String.Slice` here because that type is not `LawfulBEq` apparently.
structure MonkeyName where
  value : String
deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Hashable

inductive Operation where
  | plus: Operation
  | minus: Operation
  | times: Operation
  | div: Operation

instance: ToString Operation where
  toString op := match op with
  | Operation.plus => "+"
  | Operation.minus => "-"
  | Operation.times => "*"
  | Operation.div => "/"

def Operation.apply (op: Operation) (a b: Rat): Rat := match op with
  | plus => a + b
  | minus => a - b
  | times => a * b
  | div => a / b

def Operation.parse (input: String.Slice): Result Operation :=
  if input == "+" then Except.ok Operation.plus
  else if input == "-" then Except.ok Operation.minus
  else if input == "*" then Except.ok Operation.times
  else if input == "/" then Except.ok Operation.div
  else Except.error "Failed to parse op"

structure HumanExpression where
  coefficient: Rat
  constant: Rat

instance: ToString HumanExpression where
  toString exp := s!"({exp.coefficient}) * human + ({exp.constant})"

def HumanExpression.negate (exp: HumanExpression): HumanExpression :=
  ⟨-exp.coefficient, -exp.constant⟩

def HumanExpression.add (exp: HumanExpression) (b: Rat): HumanExpression :=
  ⟨exp.coefficient, exp.constant + b⟩

def HumanExpression.subtract (exp: HumanExpression) (b: Rat): HumanExpression :=
  ⟨exp.coefficient, exp.constant - b⟩

def HumanExpression.multiply (exp: HumanExpression) (b: Rat): HumanExpression :=
  ⟨exp.coefficient * b, exp.constant * b⟩

def HumanExpression.divide (exp: HumanExpression) (b: Rat): HumanExpression :=
  ⟨exp.coefficient / b, exp.constant / b⟩

inductive Value where
  | constant (a: Rat): Value
  | human (exp: HumanExpression): Value
deriving Nonempty

instance: ToString Value where
  toString v := match v with
  | Value.constant a => ToString.toString a
  | Value.human exp => ToString.toString exp

def Value.assertConstant (x: Value): Rat := match x with
  | constant a => a
  | human _ => dbgTrace "Value.assertConstant failed!" fun () => 0

def Value.negate (x: Value): Value := match x with
  | constant a => constant (-a)
  | human exp => human exp.negate

def Value.add (x: Value) (b: Rat): Value := match x with
  | constant a => constant (a + b)
  | human exp => human (exp.add b)

def Value.subtract (x: Value) (b: Rat): Value := match x with
  | constant a => constant (a - b)
  | human exp => human (exp.subtract b)

def Value.multiply (x: Value) (b: Rat): Value := match x with
  | constant a => constant (a * b)
  | human exp => human (exp.multiply b)

def Value.divide (x: Value) (b: Rat): Value := match x with
  | constant a => constant (a / b)
  | human exp => human (exp.divide b)

def Operation.applyV (op: Operation) (x y: Value): Value := match op with
  | plus => match x with
    | Value.constant a => y.add a
    | Value.human exp => Value.human (exp.add y.assertConstant)
  | minus => match x with
    | Value.constant a => y.negate.add a
    | Value.human exp => Value.human (exp.subtract y.assertConstant)
  | times => match x with
    | Value.constant a => y.multiply a
    | Value.human exp => Value.human (exp.multiply y.assertConstant)
  | div => match x with
    | Value.constant a => Value.constant (a / y.assertConstant)
    | Value.human exp => Value.human (exp.divide y.assertConstant)

structure ResolvedMonkey where
  name: MonkeyName
  value: Value

inductive DepExp (m: MonkeyName) where
  | single (name: MonkeyName) (op: Operation) (value: Value): DepExp m
  | double (name: MonkeyName) (op: Operation) (snd: MonkeyName): DepExp m

structure State where
  inputs: Std.Queue ResolvedMonkey
  depends: Std.DHashMap MonkeyName (fun m => List (DepExp m))
  rootDeps: MonkeyName × MonkeyName

def State.empty: State := ⟨Std.Queue.empty, ∅, (⟨""⟩, ⟨""⟩)⟩

def State.pushValue (state: State) (name: MonkeyName) (value: Value): State :=
  ⟨state.inputs.enqueue ⟨name, value⟩, state.depends, state.rootDeps⟩

def State.pushDep (state: State) (dep: MonkeyName) (exp: DepExp dep): State :=
  let map := match state.depends.get? dep with
    | none => state.depends.insert dep [exp]
    | some list => state.depends.insert dep (exp :: list)
  ⟨state.inputs, map, state.rootDeps⟩

def State.pushResolution (a: Value) (state: State) (exp: DepExp m): State :=
  match exp with
  | DepExp.single name op b => state.pushValue name (op.applyV b a)
  | DepExp.double name op snd =>
    if snd = m then state.pushValue name (op.applyV a a)
    else state.pushDep snd (DepExp.single name op a)

-- Includes setting the names that go Rato the root expression (`State.rootDeps`).
def handleRoot (state: State) (exp: String.Slice): Result State :=
  let name: MonkeyName := ⟨"root"⟩
  match (exp.trimAscii.split " ").toList with
  | [dep1, op, dep2] =>
      let dep: MonkeyName := ⟨dep1.toString⟩
      let snd: MonkeyName := ⟨dep2.toString⟩
      let state: State := ⟨state.inputs, state.depends, (dep, snd)⟩
      (Operation.parse op).map (
        fun op =>
          state.pushDep dep (DepExp.double name op snd)
      )
  | _ => Except.error "Failed to parse root expression"

def parseLine
  (humanHandler: String.Slice → Result Value)
  (state: State)
  (line: String.Slice): Result State
:=
  match (line.split ":").toList with
  | [name, exp] =>
    let name: MonkeyName := ⟨name.toString⟩
    if name.value == "humn" then (humanHandler exp.trimAscii).map (fun value => state.pushValue name value)
    else if name.value == "root" then handleRoot state exp
    else match (exp.trimAscii.split " ").toList with
    | [number] =>
      match number.toInt? with
      | none => Except.error "Failed to parse Rat"
      | some value => Except.ok (state.pushValue name (Value.constant value))
    | [dep1, op, dep2] =>
      let dep: MonkeyName := ⟨dep1.toString⟩
      let snd: MonkeyName := ⟨dep2.toString⟩
      (Operation.parse op).map (
        fun op =>
          state.pushDep dep (DepExp.double name op snd)
      )
    | _ => Except.error "Failed to parse expression"
  | _ => Except.error "Failed to parse line"

def parseHumanAsNumber (number: String.Slice): Result Value :=
  match number.toInt? with
  | none => Except.error s!"Failed to parse human Rat {number}"
  | some value => Except.ok (Value.constant value)

def parseHumanAsExp (_: String.Slice): Result Value :=
  Except.ok (Value.human {
    coefficient := 1
    constant := 0
  })

-- Proving this function terminates is tricky because the queue
-- does not shrink over time. We re-enqueue monkeys because the map
-- is strict about the order in which it gets the inputs (the first
-- one must come first), so it's possible we will need to use the same
-- monkey more than once if it appears in the second position, but
-- the first position variable has not been filled yet.
-- So the termination condition is really that `root` will eventually have
-- a value, but that seems like a hard thing to state and check.
partial def State.rootValue (state: State): Value :=
  match state.inputs.dequeue? with
  | none => dbgTrace "Unreachable; the queue never shrinks" fun () => Value.constant 0
  | some ⟨monkey, queue⟩ =>
    if monkey.name.value == "root" then monkey.value
    else
      match state.depends.get? monkey.name with
      | none => State.rootValue ⟨queue.enqueue monkey, state.depends, state.rootDeps⟩
      | some deps =>
        let state: State := ⟨queue.enqueue monkey, state.depends.erase monkey.name, state.rootDeps⟩
        let state := deps.foldl (State.pushResolution monkey.value) state
        state.rootValue

def solveForHuman (v1 v2: Value): Rat := match v1 with
  | Value.constant a => match v2 with
    | Value.human ⟨coefficient, constant⟩ => (a - constant) / coefficient
    | Value.constant _ => dbgTrace "Only one human allowed!" fun () => 0
  | Value.human ⟨coefficient, constant⟩ =>
    let a := v2.assertConstant
    (a - constant) / coefficient

partial def State.sndHumanValue (state: State) (v1: Value) (awaiting: MonkeyName): Rat :=
  match state.inputs.dequeue? with
  | none => dbgTrace "Unreachable; the queue never shrinks" fun () => 0
  | some ⟨monkey, queue⟩ =>
    if monkey.name.value == awaiting.value then solveForHuman v1 monkey.value
    else
      match state.depends.get? monkey.name with
      | none => State.sndHumanValue ⟨queue.enqueue monkey, state.depends, state.rootDeps⟩ v1 awaiting
      | some deps =>
        let state: State := ⟨queue.enqueue monkey, state.depends.erase monkey.name, state.rootDeps⟩
        let state := deps.foldl (State.pushResolution monkey.value) state
        state.sndHumanValue v1 awaiting

partial def State.humanValue (state: State): Rat :=
  match state.inputs.dequeue? with
  | none => dbgTrace "Unreachable; the queue never shrinks" fun () => 0
  | some ⟨monkey, queue⟩ =>
    if monkey.name.value == state.rootDeps.fst.value then
      let state: State := ⟨queue.enqueue monkey, state.depends.erase monkey.name, state.rootDeps⟩
      state.sndHumanValue monkey.value state.rootDeps.snd
    else if monkey.name.value == state.rootDeps.snd.value then
      let state: State := ⟨queue.enqueue monkey, state.depends.erase monkey.name, state.rootDeps⟩
      state.sndHumanValue monkey.value state.rootDeps.fst
    else
      match state.depends.get? monkey.name with
      | none => State.humanValue ⟨queue.enqueue monkey, state.depends, state.rootDeps⟩
      | some deps =>
        let state: State := ⟨queue.enqueue monkey, state.depends.erase monkey.name, state.rootDeps⟩
        let state := deps.foldl (State.pushResolution monkey.value) state
        state.humanValue

def part1Solution (input: String): Result Value := do
  let state ← (input.trimAscii.split "\n").foldM (parseLine parseHumanAsNumber) State.empty
  pure state.rootValue

def part2Solution (input: String): Result Rat := do
  let state ← (input.trimAscii.split "\n").foldM (parseLine parseHumanAsExp) State.empty
  pure state.humanValue
