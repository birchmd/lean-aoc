import AdventOfCode.Year2022.Day6

def inputIO: IO String := IO.FS.readFile ".data/2022/day6.txt"

def main : IO Unit := do
  let s1 <- inputIO.map part1Solution
  IO.println s1
  let s2 <- inputIO.map part2Solution
  IO.println s2
