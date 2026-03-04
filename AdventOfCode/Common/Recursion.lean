import Std.Data.HashMap

inductive RecOutput α β where
  | value (result: β): RecOutput α β
  | recursive (args: α): RecOutput α β
  | map (out: RecOutput α β) (f: β → β): RecOutput α β
  | bind (out: RecOutput α β) (f: β → RecOutput α β): RecOutput α β

-- Add caching (memoization) to a recursive function.
-- Example:
-- ```lean
-- def fib (n: Nat): RecOutput Nat Nat :=
--   if n = 0 then RecOutput.value 1
--   else if n = 1 then RecOutput.value 1
--   else (RecOutput.recursive (n - 1)).bind (
--     fun f1 => (RecOutput.recursive (n - 2)).map (
--       fun f2 => f1 + f2
--     )
--   )
--
-- def cachedFib (n: Nat): Nat := (cachedRecursiveFn fib n ∅).fst
-- ```
partial def cachedRecursiveFn [BEq α] [Hashable α] [Nonempty β] (f: α → RecOutput α β) (args: α) (cache: Std.HashMap α β): β × (Std.HashMap α β):=
  match cache.get? args with
  | some output => (output, cache)
  | none =>
    let ⟨result, cache⟩ := handleOutput (f args) cache
    let cache := cache.insert args result
    (result, cache)
  where handleOutput (output: RecOutput α β) (cache: Std.HashMap α β): β × (Std.HashMap α β) :=
    match output with
      | RecOutput.value result => (result, cache)
      | RecOutput.recursive newArgs => cachedRecursiveFn f newArgs cache
      | RecOutput.map out transform =>
        let ⟨result, cache⟩ := handleOutput out cache
        let result := transform result
        (result, cache)
      | RecOutput.bind out transform =>
        let ⟨result, cache⟩ := handleOutput out cache
        handleOutput (transform result) cache
