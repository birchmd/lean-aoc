import AdventOfCode.Common.Result

def parseSnafu (input: String.Slice): Result Int :=
  input.chars.foldM (
    fun acc c => match c with
    | '2' => Except.ok (5 * acc + 2)
    | '1' => Except.ok (5 * acc + 1)
    | '0' => Except.ok (5 * acc)
    | '-' => Except.ok (5 * acc - 1)
    | '=' => Except.ok (5 * acc - 2)
    | _ => Except.error "Unknown SNAFU digit"
  ) 0

-- Helper function that returns the smallest power of 5 that is greater than `x`
def power5 (x: Nat) : Nat :=
  loop 5 (by omega) x
where loop (p5: Nat) (h: 0 < p5) (x: Nat): Nat :=
  if x < p5 then p5
  else if x = p5 then 5 * p5
  else loop (5 * p5) (by omega) x
termination_by x - p5

-- An n-digit SNAFU number can represent any integer in the range
-- `[-(5^n - 1)/2, (5^n - 1)/2]`; therefore we first figure out
-- the smallest `n` such that `2|x| < 5^n`. Then we know that
-- `x` itself is in the n-digit SNAFU range and hence
-- `x + (5^n - 1) / 2` is in the range `[0, 5^n - 1]`. Such
-- numbers can be represented by a normal n-digit base-5 number.
-- To get the final SNAFU representation of `x` we just have
-- to subtract off the `(5^n - 1) / 2`, which is equivalent to
-- subtracting 2 from all the base 5 digits, yielding the desired
-- SNAFU digits.
def toSnafu (x: Int): String :=
  let p5 := power5 (2 * x.natAbs)
  let y := (x + (p5 - 1) / 2).natAbs
  let digits := (Nat.toDigits 5 y).map (
    fun d => match d with
    | '4' => '2'
    | '3' => '1'
    | '2' => '0'
    | '1' => '-'
    | '0' => '='
    | _ => '*'
  )
  String.ofList digits

def part1Solution (input: String): Result String := do
  let sum ← (input.trimAscii.split "\n").foldM (
    fun acc line => (parseSnafu line).map (fun x => x + acc)
  ) 0
  pure (toSnafu sum)

structure MerryChristmas where
deriving BEq

instance: ToString MerryChristmas where
  toString _ := "Merry Christmas!"

-- Day 25 doesn't have a part 2, so we just write "Merry Christmas" :)
def part2Solution (_: String): MerryChristmas := MerryChristmas.mk

-- Theorems proving `power5` correctness.
theorem power5_loop_gt (x p5: Nat) (h: 0 < p5): x < power5.loop p5 h x := by
  unfold power5.loop
  if h1: x < p5 then grind
  else if h2: x = p5 then grind
  else
    simp [h1, h2]
    exact power5_loop_gt x (5 * p5) (by omega)

theorem power5_gt (x: Nat): x < power5 x := by
  unfold power5
  exact power5_loop_gt x 5 (by omega)

theorem power5_loop_power
  (x p5: Nat)
  (h1: 0 < p5)
  (h2: ∃m: Nat, p5 = 5 ^ m): ∃n: Nat, power5.loop p5 h1 x = 5 ^ n
:= by
  unfold power5.loop
  if h3: x < p5 then grind
  else if h4: x = p5 then
    simp [h4]
    cases h2 with
    | intro m h5 => exists m + 1; grind
  else
    simp [h3, h4]
    have h5: ∃n: Nat, 5 * p5 = 5^n := by cases h2 with
      | intro m h6 => exists m + 1; grind
    exact power5_loop_power x (5 * p5) (by omega) h5

theorem power5_is_power (x: Nat): ∃n: Nat, power5 x = 5 ^ n := by
  unfold power5
  exact power5_loop_power x 5 (by omega) (by exists 1)

-- I would like to prove the theorem below; certainly I know it
-- is true. But I think I need to wait for Lean v4.29.0 to come out
-- because that release contains some new theorems about `Nat.toDigit`
-- which would be useful since my implementation is built on top of
-- that function.
-- theorem snafu_round_trip (x: Int): parseSnafu (toSnafu x) = Except.ok x
