 import Mathlib

def fullyContains(pairs: (Nat × Nat) × (Nat × Nat)): Bool :=
  match pairs with
  | (p1, p2) =>
    let union := match p1 with
    | (a, b) => match p2 with
      | (c, d) => (min a c, max b d)
    (union == p1) ∨ (union == p2)

def overlaps(pairs: (Nat × Nat) × (Nat × Nat)): Bool :=
  match pairs with
  | (p1, p2) =>
    match p1 with
    | (a, b) => match p2 with
      | (c, d) => (max a c) ≤ (min b d)

def parsePair(input: String.Slice) (sep: String) (f: String.Slice -> Option α): Option (α × α) :=
  match ((input.split sep).map f).toList with
  | (some x) :: (some y) :: [] => some (x, y)
  | _ => none

def parsePairs(line: String.Slice): Option ((Nat × Nat) × (Nat × Nat)) :=
  parsePair line "," (fun input => parsePair input "-" String.Slice.toNat?)

def solution(input: String) (f: (Nat × Nat) × (Nat × Nat) -> Bool): Nat :=
  let pairs := ((input.trimAscii.split "\n").filterMap parsePairs)
  (pairs.filter f).count

def part1Solution(input: String): Nat := solution input fullyContains
def part2Solution(input: String): Nat := solution input overlaps

-- Proofs for `fullyContains` and `overlaps`
def range (lb ub: Nat): Set Nat := {n | lb ≤ n ∧ n ≤ ub}

lemma range_contains (a b c d : Nat) (hx: a ≤ c ∧ d ≤ b): (range c d) ⊆ (range a b) := by
  repeat rw [range]
  intro h hw
  constructor
  . simp_all!
    omega
  simp_all!
  omega

theorem fully_contains_works (a b c d : Nat) (h: fullyContains ((a, b), (c, d)) = true): (range a b) ⊆ (range c d) ∨ (range c d) ⊆ (range a b) := by
  simp [fullyContains] at h
  cases h with
  | inl h =>
  . right
    exact range_contains a b c d h
  | inr h =>
  . left
    exact range_contains c d a b h

theorem overlaps_works (a b c d : Nat) (h: overlaps ((a, b), (c, d)) = true): ∃ x: Nat, x ∈ ((range a b) ∩ (range c d)) := by
  simp [overlaps] at h
  repeat rw [range]
  have hle: a ≤ c ∨ c ≤ a := Nat.le_total a c
  cases hle with
  | inl h =>
  . use c
    simp_all!
  | inr h =>
  . use a
    simp_all!
