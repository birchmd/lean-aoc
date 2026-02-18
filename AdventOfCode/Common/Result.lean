def Result(α : Type): Type := Except String α

instance : Applicative Result where
  pure := Except.ok
  seq mf mx := mf.bind (fun f => (mx ()).map f)

instance : Bind Result where
  bind := Except.bind

instance : Monad Result where

instance [ToString α] : ToString (Result α) where
  toString r := match r with
  | Except.error e => e
  | Except.ok x => ToString.toString x

def getOrErr (mx: Option α) (e: String): Result α :=
  (mx.map Except.ok).getD (Except.error e)
