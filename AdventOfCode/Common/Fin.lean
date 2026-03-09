-- If we have an element of `Fin n` then `n` cannot be zero.
theorem Fin.have_fin_means_non_empty (index: Fin n): 0 < n := by
  let m := index.val
  have h1: m < n := index.is_lt
  have h2: 0 ≤ m := Nat.zero_le m
  omega

def Fin.saturatingSucc (i: Fin n): Fin n :=
  let j := i.val + 1
  if h: j < n then ⟨j, h⟩
  else ⟨n - 1, by omega⟩

def Fin.saturatingPred (i: Fin n): Fin n :=
  let j := i.val - 1
  ⟨j, by omega⟩

def Fin.wrappingSucc (i: Fin n): Fin n :=
  let j := i.val + 1
  if h: j < n then ⟨j, h⟩
  else ⟨0, have_fin_means_non_empty i⟩

def Fin.wrappingPred (i: Fin n): Fin n :=
  have h: 0 < n := have_fin_means_non_empty i
  if i.val = 0 then ⟨n - 1, by omega⟩
  else
    let j := i.val - 1
    ⟨j, by omega⟩

theorem mod_in_bounds (a b: Nat) (h: b ≠ 0): a % b < b := by
  let c := a % b
  have h1: a % b = c := by trivial
  rw [Nat.mod_eq_iff] at h1
  grind

def finMod (a b: Nat) (h: b ≠ 0): Fin b := ⟨a % b, mod_in_bounds a b h⟩

-- Given a property `p` over some type `α`, an element `base: α` for which
-- `p` holds, and a function `f` which preserves the property `p`, then
-- `p` will hold on the output of a fold performed using `f`.
theorem loop_invariant
  (p: α → Prop)
  (n: Nat)
  (base: α)
  (base_case: p base)
  (f: α → Fin n → α)
  (loop_inv: (x: α) → (k: Fin n) → (p x) → p (f x k)): p (Fin.foldl n f base)
:= by
  cases n with
  | zero =>
    simp [Fin.foldl_zero]
    trivial
  | succ m =>
    simp [Fin.foldl_succ]
    let g: α → Fin m → α := (fun x i => f x i.succ)
    let b: α := f base 0
    have h1: g = (fun x i => f x i.succ) := by trivial
    have h2: b = f base 0 := by trivial
    have new_base_case: p b := by grind
    rw [← h1]
    rw [← h2]
    have new_loop_inv: (x: α) → (k: Fin m) → (p x) → p (g x k) := by grind
    exact loop_invariant p m b new_base_case g new_loop_inv
