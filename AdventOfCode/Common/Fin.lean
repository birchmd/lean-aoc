-- If we have an element of `Fin n` then `n` cannot be zero.
theorem Fin.have_fin_means_non_empty (index: Fin n): 0 < n := by
  let m := index.val
  have h1: m < n := index.is_lt
  have h2: 0 ≤ m := Nat.zero_le m
  omega


def Fin.wrappingSucc (i: Fin n): Fin n :=
  let j := i.val + 1
  if h: j < n then ⟨j, h⟩
  else ⟨0, have_fin_means_non_empty i⟩
