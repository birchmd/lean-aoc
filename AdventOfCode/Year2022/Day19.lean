import AdventOfCode.Common.Recursion
import AdventOfCode.Common.Result
import Std.Data.HashMap

structure Ore where
  amount: Nat
deriving BEq, Hashable

instance: LE Ore where
  le x y := x.amount ≤ y.amount

instance: DecidableLE Ore :=
  fun x y => inferInstanceAs (Decidable (x.amount ≤ y.amount))

structure Clay where
  amount: Nat
deriving BEq, Hashable

instance: LE Clay where
  le x y := x.amount ≤ y.amount

instance: DecidableLE Clay :=
  fun x y => inferInstanceAs (Decidable (x.amount ≤ y.amount))

structure Obsidian where
  amount: Nat
deriving BEq, Hashable

instance: LE Obsidian where
  le x y := x.amount ≤ y.amount

instance: DecidableLE Obsidian :=
  fun x y => inferInstanceAs (Decidable (x.amount ≤ y.amount))

structure Blueprint where
  id: Nat
  ore_robot_cost: Ore
  clay_robot_cost: Ore
  obsidian_robot_cost: Ore × Clay
  geode_robot_cost: Ore × Obsidian
  max_ore_cost: Ore
  max_clay_cost: Clay
  max_obsidian_cost: Obsidian

inductive FactoryAction where
  | NoAction: FactoryAction
  | BuildOreRobot: FactoryAction
  | BuildClayRobot: FactoryAction
  | BuildObsidianRobot: FactoryAction
  | BuildGeodeRobot: FactoryAction

structure WorldState where
  time: Nat
  ore: Ore
  clay: Clay
  obsidian: Obsidian
  oreRobots: Nat
  clayRobots: Nat
  obsidianRobots: Nat
  geodeRobots: Nat
deriving BEq, Hashable

def WorldState.start (time: Nat): WorldState := {
  time := time
  ore := { amount := 0 }
  clay := { amount := 0 }
  obsidian := { amount := 0 }
  oreRobots := 1
  clayRobots := 0
  obsidianRobots := 0
  geodeRobots := 0
}

-- Don't make more of any basic resource than you can use
-- each minute to make more bots (it's inefficient).
def WorldState.hasExcessiveProduction (s: WorldState) (b: Blueprint): Bool :=
  (b.max_ore_cost.amount < s.oreRobots) ∨
    (b.max_clay_cost.amount < s.clayRobots) ∨
    (b.max_obsidian_cost.amount < s.obsidianRobots)

def timeStep (state: WorldState) (action: FactoryAction) (blueprint: Blueprint): WorldState := match action with
| FactoryAction.NoAction => {
  time := state.time - 1
  ore := { amount := state.ore.amount + state.oreRobots }
  clay := { amount := state.clay.amount + state.clayRobots }
  obsidian := { amount := state.obsidian.amount + state.obsidianRobots }
  oreRobots := state.oreRobots
  clayRobots := state.clayRobots
  obsidianRobots := state.obsidianRobots
  geodeRobots := state.geodeRobots
}
| FactoryAction.BuildOreRobot => {
  time := state.time - 1
  ore := { amount := state.ore.amount + state.oreRobots - blueprint.ore_robot_cost.amount }
  clay := { amount := state.clay.amount + state.clayRobots }
  obsidian := { amount := state.obsidian.amount + state.obsidianRobots }
  oreRobots := state.oreRobots + 1
  clayRobots := state.clayRobots
  obsidianRobots := state.obsidianRobots
  geodeRobots := state.geodeRobots
}
| FactoryAction.BuildClayRobot => {
  time := state.time - 1
  ore := { amount := state.ore.amount + state.oreRobots - blueprint.clay_robot_cost.amount }
  clay := { amount := state.clay.amount + state.clayRobots }
  obsidian := { amount := state.obsidian.amount + state.obsidianRobots }
  oreRobots := state.oreRobots
  clayRobots := state.clayRobots + 1
  obsidianRobots := state.obsidianRobots
  geodeRobots := state.geodeRobots
}
| FactoryAction.BuildObsidianRobot => {
  time := state.time - 1
  ore := { amount := state.ore.amount + state.oreRobots - blueprint.obsidian_robot_cost.fst.amount }
  clay := { amount := state.clay.amount + state.clayRobots - blueprint.obsidian_robot_cost.snd.amount }
  obsidian := { amount := state.obsidian.amount + state.obsidianRobots }
  oreRobots := state.oreRobots
  clayRobots := state.clayRobots
  obsidianRobots := state.obsidianRobots + 1
  geodeRobots := state.geodeRobots
}
| FactoryAction.BuildGeodeRobot => {
  time := state.time - 1
  ore := { amount := state.ore.amount + state.oreRobots - blueprint.geode_robot_cost.fst.amount }
  clay := { amount := state.clay.amount + state.clayRobots }
  obsidian := { amount := state.obsidian.amount + state.obsidianRobots - blueprint.geode_robot_cost.snd.amount }
  oreRobots := state.oreRobots
  clayRobots := state.clayRobots
  obsidianRobots := state.obsidianRobots
  geodeRobots := state.geodeRobots + 1
}

def nGeodes (blueprint: Blueprint) (state: WorldState): RecOutput WorldState Nat :=
  if state.time = 0 then RecOutput.value 0
  else if state.hasExcessiveProduction blueprint then RecOutput.value 0
  else
    -- Take the maximum result over of all the possible actions we could do
    let out := RecOutput.recursive (timeStep state FactoryAction.NoAction blueprint)
    let out := out.bind (
      fun noAction =>
        if blueprint.ore_robot_cost ≤ state.ore then
          (RecOutput.recursive (timeStep state FactoryAction.BuildOreRobot blueprint)).map (
            fun buildOreBot => max noAction buildOreBot
          )
        else RecOutput.value noAction
    )
    let out := out.bind (
      fun result =>
        if blueprint.clay_robot_cost ≤ state.ore then
          (RecOutput.recursive (timeStep state FactoryAction.BuildClayRobot blueprint)).map (
            fun buildClayBot => max result buildClayBot
          )
        else RecOutput.value result
    )
    let out := out.bind (
      fun result =>
        if blueprint.obsidian_robot_cost.fst ≤ state.ore ∧ blueprint.obsidian_robot_cost.snd ≤ state.clay then
          (RecOutput.recursive (timeStep state FactoryAction.BuildObsidianRobot blueprint)).map (
            fun buildObsBot => max result buildObsBot
          )
        else RecOutput.value result
    )
    let out := out.bind (
      fun result =>
        if blueprint.geode_robot_cost.fst ≤ state.ore ∧ blueprint.geode_robot_cost.snd ≤ state.obsidian then
          (RecOutput.recursive (timeStep state FactoryAction.BuildGeodeRobot blueprint)).map (
            -- Geode Robot will make 1 geode per unit of time left.
            fun buildGeoBot => max result (buildGeoBot + state.time - 1)
          )
        else RecOutput.value result
    )
    out

def Blueprint.quality (blueprint: Blueprint): Nat :=
  let ⟨result, _⟩ := cachedRecursiveFn (nGeodes blueprint) (WorldState.start 24) ∅
  result * blueprint.id

def String.Slice.takeUntil (s: String.Slice) (c: Char): String.Slice :=
  match (s.split c).toList with
  | [] => s
  | head :: _ => head

def parseBlueprint (line: String.Slice): Result Blueprint :=
  let line := line.dropPrefix "Blueprint "
  let id := getOrErr (line.takeUntil ':').toNat? "Failed to parse blueprint id"
  id >>= ( fun id =>
    let numbers := ((line.split " ").filterMap String.Slice.toNat?).toList
    match numbers with
    | orc :: crc :: oroc :: orcc :: groc :: grbc :: [] =>
      Except.ok {
        id := id
        ore_robot_cost := { amount := orc }
        clay_robot_cost := { amount := crc }
        obsidian_robot_cost := ({ amount := oroc }, { amount := orcc })
        geode_robot_cost := ({ amount := groc }, { amount := grbc })
        max_ore_cost := { amount := [orc, crc, oroc, groc].max (by grind) }
        max_clay_cost := { amount := orcc }
        max_obsidian_cost := { amount := grbc }
      }
    | _ => Except.error "Failed to parse blueprint"
  )

def part1Solution(input: String): Result Nat :=
  ((input.trimAscii.split "\n").mapM parseBlueprint).fold (
    fun acc bp => acc + bp.quality
  ) 0

def part2Solution(input: String): Result Nat :=
  (((input.trimAscii.split "\n").mapM parseBlueprint).take 3).fold (
    fun acc bp => acc * (cachedRecursiveFn (nGeodes bp) (WorldState.start 32) ∅).fst
  ) 1
