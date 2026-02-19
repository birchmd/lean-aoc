def Except.take (result: Except α α): α :=
  match result with
  | Except.error a => a
  | Except.ok a => a
