def Elf := List Nat

def parseElf(block: String.Slice): Elf :=
  ((block.split "\n").map String.Slice.toNat!).toList

def parseInput(input: String): List Elf :=
  ((input.trimAscii.split "\n\n").map parseElf).toList

def elfTotal(elf: Elf): Nat := elf.foldl Nat.add 0

def inputMax(input: List Elf): Nat := (input.map elfTotal).max?.getD 0

def sumLastThree(xs: List Nat): Nat :=
  match xs with
  | [] => 0
  | x :: [] => x
  | x :: y :: [] => x + y
  | x :: y :: z :: [] => x + y + z
  | _ :: tail => sumLastThree tail

def inputTop3(input: List Elf): Nat :=
  (input.map elfTotal).mergeSort |> sumLastThree

def part1Solution (input: String): Nat := input
  |> parseInput
  |> inputMax

def part2Solution (input: String): Nat := input
  |> parseInput
  |> inputTop3
