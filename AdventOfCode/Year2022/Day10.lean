import AdventOfCode.Common.Result

inductive Ready where
  | unit: Ready

inductive Noop where
  | unit: Noop

inductive StartAddx (v: Int) where
  | unit: StartAddx v

inductive EndAddx (v: Int) where
  | unit: EndAddx v

inductive Instruction where
  | noop (inner: Noop): Instruction
  | addx (v: Int) (inner: StartAddx v): Instruction

structure Cpu α where
  x: Int
  cycle: Nat
  processing: α

def Cpu.start: Cpu Ready := ⟨1, 1, Ready.unit⟩

class Ticker (α: Type u) where
  nextState: Type u
  tick: α → nextState

def loadInst (inst: α) (cpu: Cpu Ready): Cpu α :=
  ⟨cpu.x, cpu.cycle, inst⟩

instance : Ticker (Cpu Noop) where
  nextState := Cpu Ready
  tick cpu := ⟨cpu.x, cpu.cycle + 1, Ready.unit⟩

instance : Ticker (Cpu (StartAddx v)) where
  nextState := Cpu (EndAddx v)
  tick cpu := ⟨cpu.x, cpu.cycle + 1, EndAddx.unit⟩

instance : Ticker (Cpu (EndAddx v)) where
  nextState := Cpu Ready
  tick cpu := ⟨cpu.x + v, cpu.cycle + 1, Ready.unit⟩

def exeInst (cycleCallback: {β: Type} → Cpu β → α → α) (stateCpu: α × (Cpu Ready)) (inst: Instruction): α × (Cpu Ready) :=
  let ⟨state, cpu⟩ := stateCpu
  match inst with
  | Instruction.noop inner =>
    let loaded := loadInst inner cpu
    let state := cycleCallback loaded state
    (state, Ticker.tick loaded)
  | Instruction.addx v inner =>
    let loaded: Cpu (StartAddx v) := loadInst inner cpu
    let state := cycleCallback loaded state
    let started: Cpu (EndAddx v) := Ticker.tick loaded
    let state := cycleCallback started state
    (state, Ticker.tick started)

def parseInst (line: String.Slice): Result Instruction :=
  if line == "noop" then
    Except.ok (Instruction.noop Noop.unit)
  else if line.startsWith "addx" then
    match (line.split " ").toList with
    | _ :: v :: [] =>
      let v := getOrErr v.toInt? "Failed to parse addx number"
      v.map (fun v => Instruction.addx (v := v) StartAddx.unit)
    | _ => Except.error "Failed to parse addx line"
  else
    Except.error "Unknown instruction"

structure State1 where
  waitingFor: Nat
  total: Int

def State1.start: State1 := ⟨20, 0⟩

def part1Callback (cpu: Cpu α) (state: State1): State1 :=
  if cpu.cycle = state.waitingFor then
    let signalStrength := cpu.cycle * cpu.x
    ⟨state.waitingFor + 40, state.total + signalStrength⟩
  else state

structure State2 where
  buffer: String
  pixelPosition: Int

def State2.start: State2 := ⟨"", 0⟩

def part2Callback (cpu: Cpu α) (state: State2): State2 :=
  let d := cpu.x - state.pixelPosition
  let isLit := d = 0 ∨ d = -1 ∨ d = 1
  let draw := if isLit then '#' else '.'
  let nextPixel := (state.pixelPosition + 1) % 40
  let buffer := state.buffer.push draw
  let buffer := if nextPixel = 0 then buffer.push '\n' else buffer
  ⟨buffer, nextPixel⟩

def part1Solution(input: String): Result Int := do
  let ⟨state, _⟩ ← ((input.trimAscii.split "\n").mapM parseInst).fold (exeInst part1Callback) (State1.start, Cpu.start)
  pure state.total

def part2Solution(input: String): Result String := do
  let ⟨state, _⟩ ← ((input.trimAscii.split "\n").mapM parseInst).fold (exeInst part2Callback) (State2.start, Cpu.start)
  pure state.buffer
